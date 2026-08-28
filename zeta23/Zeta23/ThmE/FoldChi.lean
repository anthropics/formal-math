/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmE/FoldChi.lean — the symmetry fold for Λ_sym(s,χ) (χ-analogue of
Zeta23/RvM/Fold.lean), used in the assembly of the zero count for L(s,χ).

Global symmetries (primitive χ mod q > 1; everything is entire, so no side conditions):
  Λ(w,χ⁻¹) = conj Λ(w̄,χ)   (identity theorem from Λ = γ·L on Re > 0 + SeamL.LFunction_conj),
  Λ_sym(1−w,χ) = W(χ)·Λ_sym(w,χ⁻¹)  (CountByIntegralChi.completedLSym_one_sub), hence
  (Λ_sym'/Λ_sym)(1−s̄,χ) = −conj (Λ_sym'/Λ_sym)(s,χ)  for every s.
Folding the rectangle ∂([−1,2]×[T₁,T₂]) onto its right half exactly as for ζ:
  ∮ Λ_sym'/Λ_sym = 2i·Im(halfContour (Λ_sym'/Λ_sym) T₁ T₂),  so with CountByIntegralChi
  N_χ(T₁,T₂) = (1/π)·Im(halfContour (logDeriv (completedLSym χ)) T₁ T₂)
for good heights T₁ ≤ T₂ of any sign (Zeta23.RvM.halfContour reused verbatim).
-/
import Zeta23.ThmE.CountByIntegralChi
import Zeta23.RvM.Fold

open Complex MeasureTheory Set intervalIntegral DirichletCharacter
open scoped ComplexConjugate

noncomputable section

namespace Zeta23
namespace ThmE

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}


/-! ## χ⁻¹ is primitive when χ is -/

omit [NeZero q] in
lemma factorsThrough_inv {d : ℕ} (h : FactorsThrough χ d) : FactorsThrough χ⁻¹ d := by
  obtain ⟨hd, χ₀, hχ⟩ := h
  exact ⟨hd, χ₀⁻¹, by rw [map_inv, ← hχ]⟩

omit [NeZero q] in
lemma conductor_inv : conductor χ⁻¹ = conductor χ := by
  unfold conductor
  congr 1
  ext d
  simp only [mem_conductorSet_iff]
  constructor
  · intro h; simpa using factorsThrough_inv h
  · exact factorsThrough_inv

omit [NeZero q] in
lemma isPrimitive_inv (hprim : χ.IsPrimitive) : χ⁻¹.IsPrimitive := by
  unfold IsPrimitive at *
  rw [conductor_inv]; exact hprim

/-! ## Conjugation: Λ(w,χ⁻¹) = conj Λ(w̄,χ), and the same for Λ_sym -/

omit [NeZero q] in
lemma gammaFactor_conj (s : ℂ) : gammaFactor χ (conj s) = conj (gammaFactor χ s) := by
  rcases χ.even_or_odd with he | ho
  · rw [he.gammaFactor_def, he.gammaFactor_def, Zeta23.RvM.Gammaℝ_conj]
  · rw [ho.gammaFactor_def, ho.gammaFactor_def, ← Zeta23.RvM.Gammaℝ_conj, map_add, map_one]

omit [NeZero q] in
/-- χ⁻¹ has the same parity, hence the same Γ-factor. -/
lemma gammaFactor_inv : gammaFactor χ⁻¹ = gammaFactor χ := by
  have hunit : IsUnit (-1 : ZMod q) := isUnit_one.neg
  have hsq : χ (-1) * χ (-1) = 1 := by rw [← map_mul]; simp
  have hinv : χ⁻¹ (-1) = χ (-1) := by
    have h1 : χ⁻¹ (-1) * χ (-1) = 1 := by
      rw [← MulChar.mul_apply, inv_mul_cancel, MulChar.one_apply hunit]
    calc χ⁻¹ (-1) = χ⁻¹ (-1) * (χ (-1) * χ (-1)) := by rw [hsq, mul_one]
      _ = (χ⁻¹ (-1) * χ (-1)) * χ (-1) := by ring
      _ = χ (-1) := by rw [h1, one_mul]
  funext s
  rcases χ.even_or_odd with he | ho
  · have he' : χ⁻¹.Even := by show χ⁻¹ (-1) = 1; rw [hinv]; exact he
    rw [he.gammaFactor_def, he'.gammaFactor_def]
  · have ho' : χ⁻¹.Odd := by show χ⁻¹ (-1) = -1; rw [hinv]; exact ho
    rw [ho.gammaFactor_def, ho'.gammaFactor_def]

/-- **Λ(w,χ⁻¹) = conj Λ(w̄,χ)** for all w (χ mod q > 1 nontrivial). -/
lemma completedLFunction_inv_eq_conj (hq : 1 < q) (hχ1 : χ ≠ 1) (w : ℂ) :
    completedLFunction χ⁻¹ w = conj (completedLFunction χ (conj w)) := by
  have hA : AnalyticOnNhd ℂ (completedLFunction χ⁻¹) univ := fun z _ =>
    (differentiable_completedLFunction (inv_ne_one hχ1)).analyticAt z
  have hB : AnalyticOnNhd ℂ (fun z => conj (completedLFunction χ (conj z))) univ := by
    refine DifferentiableOn.analyticOnNhd (fun z _ => ?_) isOpen_univ
    have hd : DifferentiableAt ℂ (completedLFunction χ) (conj z) :=
      (differentiable_completedLFunction hχ1) _
    have h3 := hd.conj_conj
    rw [Complex.conj_conj] at h3
    exact h3.differentiableWithinAt
  have hagree : completedLFunction χ⁻¹ =ᶠ[nhds (2 : ℂ)]
      (fun z => conj (completedLFunction χ (conj z))) := by
    have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show (0 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    have hzc : 0 < (conj z).re := by simpa using hz
    rw [(completed_eq_gamma_mul_L (χ := χ⁻¹) hq hz).eq_of_nhds,
      (completed_eq_gamma_mul_L (χ := χ) hq hzc).eq_of_nhds]
    simp only [Pi.mul_apply, map_mul, gammaFactor_conj, Complex.conj_conj, gammaFactor_inv,
      LFunction_conj hχ1]
  have heq := hA.eqOn_of_preconnected_of_eventuallyEq hB isPreconnected_univ (mem_univ _) hagree
  exact heq (mem_univ w)

lemma completedLSym_inv_eq_conj (hq : 1 < q) (hχ1 : χ ≠ 1) (w : ℂ) :
    completedLSym χ⁻¹ w = conj (completedLSym χ (conj w)) := by
  unfold completedLSym
  rw [map_mul, completedLFunction_inv_eq_conj hq hχ1 w]
  congr 1
  have h := Zeta23.RvM.cpow_ofReal_conj (x := (q : ℝ)) (by exact_mod_cast NeZero.pos q) (conj w / 2)
  simp only [Complex.ofReal_natCast, map_div₀, Complex.conj_conj, map_ofNat] at h
  exact h

/-- logDeriv Λ_sym(s̄,χ⁻¹)… in the form we need: logDeriv (Λ_sym χ⁻¹) (conj s) = conj (logDeriv (Λ_sym χ) s). -/
lemma logDeriv_completedLSym_inv_conj (hq : 1 < q) (hχ1 : χ ≠ 1) (s : ℂ) :
    logDeriv (completedLSym χ⁻¹) (conj s) = conj (logDeriv (completedLSym χ) s) := by
  have hfun : completedLSym χ⁻¹ = fun z => conj (completedLSym χ (conj z)) :=
    funext (completedLSym_inv_eq_conj hq hχ1)
  rw [hfun, logDeriv_apply, logDeriv_apply, deriv_conj_conj', Complex.conj_conj, ← map_div₀]

/-- **The fold symmetry for Λ_sym**, valid at every point:
(Λ_sym'/Λ_sym)(1 − s̄, χ) = −conj((Λ_sym'/Λ_sym)(s, χ)). -/
theorem logDeriv_completedLSym_one_sub_conj (hq : 1 < q) (hprim : χ.IsPrimitive) (s : ℂ) :
    logDeriv (completedLSym χ) (1 - conj s) = -conj (logDeriv (completedLSym χ) s) := by
  have hχ1 := ne_one_of_primitive hq hprim
  -- from the functional equation, as an identity of functions of w
  have hcomp : (completedLSym χ) ∘ (fun u : ℂ => 1 - u) = fun w => rootNumber χ * completedLSym χ⁻¹ w := by
    funext w; exact completedLSym_one_sub hprim w
  have hd : DifferentiableAt ℂ (completedLSym χ) (1 - conj s) := differentiable_completedLSym hχ1 _
  have hg : DifferentiableAt ℂ (fun u : ℂ => 1 - u) (conj s) :=
    (differentiableAt_const _).sub differentiableAt_id
  have key := logDeriv_comp (x := conj s) hd hg
  rw [hcomp, logDeriv_const_mul _ _ (rootNumber_ne_zero hq hprim),
    logDeriv_completedLSym_inv_conj hq hχ1] at key
  have hderiv : deriv (fun u : ℂ => 1 - u) (conj s) = -1 := by
    rw [deriv_const_sub, deriv_id'']
  rw [hderiv] at key
  -- key : conj (logDeriv Λ_sym s) = logDeriv Λ_sym (1 - conj s) * (-1)
  linear_combination key

/-! ## Continuity of Λ_sym'/Λ_sym at good heights -/

lemma continuousAt_logDeriv_completedLSym (hq : 1 < q) (hprim : χ.IsPrimitive) {s : ℂ}
    (hgood : ∀ ρ, IsNontrivialZeroL χ ρ → ρ.im ≠ s.im) :
    ContinuousAt (logDeriv (completedLSym χ)) s := by
  have hχ1 := ne_one_of_primitive hq hprim
  have hΛ : AnalyticAt ℂ (completedLSym χ) s := (differentiable_completedLSym hχ1).analyticAt s
  have hne : completedLSym χ s ≠ 0 := fun h =>
    hgood s ((completedLSym_eq_zero_iff hq hprim).mp h) rfl
  exact hΛ.deriv.continuousAt.div hΛ.continuousAt hne

/-! ## The fold -/

/-- Horizontal fold at a good height T:  ∫_{−1}^{2} F(σ+iT)dσ = 2i·Im ∫_{1/2}^{2} F(σ+iT)dσ. -/
lemma horizontal_foldChi (hq : 1 < q) (hprim : χ.IsPrimitive) {T : ℝ}
    (hgood : ∀ ρ, IsNontrivialZeroL χ ρ → ρ.im ≠ T) :
    ∫ σ in (-1 : ℝ)..2, logDeriv (completedLSym χ) (σ + T * I)
      = 2 * I * ((∫ σ in (1 / 2 : ℝ)..2, logDeriv (completedLSym χ) (σ + T * I)).im : ℂ) := by
  set F := logDeriv (completedLSym χ) with hF
  have hcont : Continuous fun σ : ℝ => F (σ + T * I) := by
    refine continuous_iff_continuousAt.mpr fun σ => ?_
    have h := continuousAt_logDeriv_completedLSym hq hprim (s := σ + T * I) (by simpa using hgood)
    exact ContinuousAt.comp (f := fun σ : ℝ => (σ : ℂ) + T * I) h (by fun_prop)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) (-1) (1 / 2))
    (hcont.intervalIntegrable (μ := volume) (1 / 2) 2)
  rw [← hsplit]
  set A := ∫ σ in (1 / 2 : ℝ)..2, F (σ + T * I) with hA
  have hleft : ∫ σ in (-1 : ℝ)..(1 / 2), F (σ + T * I) = -conj A := by
    have hsub := intervalIntegral.integral_comp_sub_left (f := fun x : ℝ => F (x + T * I))
      (a := (1 / 2 : ℝ)) (b := 2) (1 : ℝ)
    norm_num at hsub
    rw [← hsub, hA, ← intervalIntegral_conj, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x _
    have key := logDeriv_completedLSym_one_sub_conj hq hprim (x + T * I)
    have e : (1 : ℂ) - conj ((x : ℂ) + T * I) = 1 - (x : ℂ) + T * I := by
      simp [Complex.ext_iff]
    simp only [hF] at key ⊢
    rw [← e, key]
  rw [hleft, neg_add_eq_sub, Complex.sub_conj]
  push_cast
  ring

/-- Vertical fold: ∫_{T₁}^{T₂} F(−1+it)dt = −conj ∫_{T₁}^{T₂} F(2+it)dt. -/
lemma vertical_foldChi (hq : 1 < q) (hprim : χ.IsPrimitive) (T₁ T₂ : ℝ) :
    ∫ t in T₁..T₂, logDeriv (completedLSym χ) (-1 + t * I)
      = -conj (∫ t in T₁..T₂, logDeriv (completedLSym χ) (2 + t * I)) := by
  rw [← intervalIntegral_conj, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro t _
  have key := logDeriv_completedLSym_one_sub_conj hq hprim (2 + t * I)
  have e : (1 : ℂ) - conj ((2 : ℂ) + t * I) = -1 + t * I := by
    simp [Complex.ext_iff]; norm_num
  show logDeriv (completedLSym χ) (-1 + t * I) = -conj (logDeriv (completedLSym χ) (2 + t * I))
  rw [← e, key]

/-- **The fold** for Λ_sym(s,χ): for good heights T₁ ≤ T₂ (any sign),
∮_{∂([−1,2]×[T₁,T₂])} Λ_sym'/Λ_sym = 2i·Im(halfContour (Λ_sym'/Λ_sym) T₁ T₂). -/
theorem rectangleIntegral_logDeriv_completedLSym_eq_halfContour (hq : 1 < q)
    (hprim : χ.IsPrimitive) {T₁ T₂ : ℝ}
    (hg1 : ∀ ρ, IsNontrivialZeroL χ ρ → ρ.im ≠ T₁) (hg2 : ∀ ρ, IsNontrivialZeroL χ ρ → ρ.im ≠ T₂) :
    RectangleIntegral (logDeriv (completedLSym χ)) (-1 + T₁ * I) (2 + T₂ * I)
      = 2 * I * ((Zeta23.RvM.halfContour (logDeriv (completedLSym χ)) T₁ T₂).im : ℂ) := by
  have hre1 : (-1 + T₁ * I).re = -1 := by simp
  have him1 : (-1 + T₁ * I).im = T₁ := by simp
  have hre2 : (2 + T₂ * I : ℂ).re = 2 := by simp
  have him2 : (2 + T₂ * I : ℂ).im = T₂ := by simp
  simp only [RectangleIntegral, HIntegral, VIntegral, hre1, him1, hre2, him2, smul_eq_mul,
    Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [horizontal_foldChi hq hprim hg1, horizontal_foldChi hq hprim hg2, vertical_foldChi hq hprim T₁ T₂]
  simp only [Zeta23.RvM.halfContour, Complex.add_im, Complex.sub_im, Complex.mul_I_im]
  generalize (∫ σ in (1 / 2 : ℝ)..2, logDeriv (completedLSym χ) (σ + T₁ * I)) = A₁
  generalize (∫ σ in (1 / 2 : ℝ)..2, logDeriv (completedLSym χ) (σ + T₂ * I)) = A₂
  generalize (∫ t in T₁..T₂, logDeriv (completedLSym χ) (2 + t * I)) = B
  have e1 : 2 * I * (A₁.im : ℂ) - 2 * I * (A₂.im : ℂ) + I * B - I * -conj B
      = 2 * I * (A₁.im : ℂ) - 2 * I * (A₂.im : ℂ) + I * (B + conj B) := by ring
  rw [e1, Complex.add_conj]
  push_cast
  ring

/-- **N_χ(T₁,T₂) = (1/π)·Im ∫_L Λ_sym'/Λ_sym** for good heights T₁ ≤ T₂ of any sign. -/
theorem NcountL_eq_im_halfContour (hq : 1 < q) (hprim : χ.IsPrimitive) {T₁ T₂ : ℝ}
    (h12 : T₁ ≤ T₂)
    (hg1 : ∀ ρ, IsNontrivialZeroL χ ρ → ρ.im ≠ T₁) (hg2 : ∀ ρ, IsNontrivialZeroL χ ρ → ρ.im ≠ T₂) :
    (NcountL χ T₁ T₂ : ℝ)
      = (1 / Real.pi) * (Zeta23.RvM.halfContour (logDeriv (completedLSym χ)) T₁ T₂).im := by
  have h := rectangleIntegral'_logDeriv_completedLSym_eq_NcountL hq hprim h12 hg1 hg2
  change (1 / (2 * Real.pi * I)) • RectangleIntegral _ _ _ = _ at h
  rw [rectangleIntegral_logDeriv_completedLSym_eq_halfContour hq hprim hg1 hg2, smul_eq_mul] at h
  have h' : ((NcountL χ T₁ T₂ : ℝ) : ℂ)
      = (((1 / Real.pi) * (Zeta23.RvM.halfContour (logDeriv (completedLSym χ)) T₁ T₂).im : ℝ) : ℂ) := by
    push_cast
    rw [← h]
    field_simp
  exact_mod_cast h'

end ThmE
end Zeta23
