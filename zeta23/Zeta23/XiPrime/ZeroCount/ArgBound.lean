/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/ZeroCount/ArgBound.lean — two generic "the argument moves by at most π" lemmas
(Mathlib only).

(A) If g : ℝ → ℂ has 0 < Re g on [a,b] then |Im ∫_a^b g′/g| ≤ π  (log g is a primitive; |arg| < π/2 at
    both ends).  Corollaries in the shapes used on the contour: the vertical segment t ↦ f(σ+it)
    (integrand logDeriv f (σ+it)·i) and the horizontal segment σ ↦ f(σ+iT).
    (Zeta23/RvM/Backlund.lean vertical_two is the instance f = ζ, σ = 2.)
(B) A single partial-fraction term along a horizontal segment: |Im ∫_a^b dσ/(σ+iT−ρ)| ≤ π.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.CauchyIntegral

open Complex Set MeasureTheory intervalIntegral

noncomputable section

namespace Zeta23
namespace XiPrime
namespace ZeroCount

/-- **(A)** positive real part along a path ⇒ the argument varies by less than π. -/
theorem abs_im_integral_logDeriv_le_pi {g g' : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hderiv : ∀ x ∈ Icc a b, HasDerivAt g (g' x) x) (hcont : ContinuousOn g' (Icc a b))
    (hre : ∀ x ∈ Icc a b, 0 < (g x).re) :
    |(∫ x in a..b, g' x / g x).im| ≤ Real.pi := by
  have hgc : ContinuousOn g (Icc a b) := fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  have hne : ∀ x ∈ Icc a b, g x ≠ 0 := fun x hx h => by
    have := hre x hx; rw [h] at this; simp at this
  have hlog : ∀ x ∈ Icc a b, HasDerivAt (fun y => Complex.log (g y)) (g' x / g x) x := by
    intro x hx
    have h1 : HasDerivAt Complex.log (g x)⁻¹ (g x) := Complex.hasDerivAt_log (Or.inl (hre x hx))
    have h := h1.comp x (hderiv x hx)
    have e : (g x)⁻¹ * g' x = g' x / g x := by field_simp
    rw [e] at h
    exact h
  have hint : IntervalIntegrable (fun x => g' x / g x) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact hcont.div hgc hne
  rw [integral_eq_sub_of_hasDerivAt (fun x hx => hlog x (by rwa [uIcc_of_le hab] at hx)) hint,
    Complex.sub_im, Complex.log_im, Complex.log_im]
  have h1 : |Complex.arg (g b)| ≤ Real.pi / 2 :=
    Complex.abs_arg_le_pi_div_two_iff.mpr (hre b ⟨hab, le_rfl⟩).le
  have h2 : |Complex.arg (g a)| ≤ Real.pi / 2 :=
    Complex.abs_arg_le_pi_div_two_iff.mpr (hre a ⟨le_rfl, hab⟩).le
  calc |Complex.arg (g b) - Complex.arg (g a)| ≤ |Complex.arg (g b)| + |Complex.arg (g a)| :=
        abs_sub _ _
    _ ≤ Real.pi / 2 + Real.pi / 2 := add_le_add h1 h2
    _ = Real.pi := by ring

/-- the vertical path t ↦ σ + it and its derivative i. -/
lemma hasDerivAt_vertical (σ t : ℝ) : HasDerivAt (fun t : ℝ => (σ : ℂ) + t * I) I t := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  simpa using (h1.mul_const I).const_add (σ : ℂ)

/-- the horizontal path σ ↦ σ + iT and its derivative 1. -/
lemma hasDerivAt_horizontal (T σ : ℝ) : HasDerivAt (fun σ : ℝ => (σ : ℂ) + T * I) 1 σ := by
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 σ := Complex.ofRealCLM.hasDerivAt
  simpa using h1.add_const ((T : ℂ) * I)

/-- **(A), vertical segment**: f analytic with Re f > 0 along σ + i[T₁,T₂] ⇒ |Im ∫ f′/f(σ+it)·i dt| ≤ π. -/
theorem abs_im_integral_logDeriv_vertical_le_pi {f : ℂ → ℂ} {σ T₁ T₂ : ℝ} (h12 : T₁ ≤ T₂)
    (hf : ∀ t ∈ Icc T₁ T₂, AnalyticAt ℂ f (σ + t * I))
    (hre : ∀ t ∈ Icc T₁ T₂, 0 < (f (σ + t * I)).re) :
    |(∫ t in T₁..T₂, logDeriv f (σ + t * I) * I).im| ≤ Real.pi := by
  set g : ℝ → ℂ := fun t => f (σ + t * I) with hg
  set g' : ℝ → ℂ := fun t => deriv f (σ + t * I) * I with hg'
  have hderiv : ∀ t ∈ Icc T₁ T₂, HasDerivAt g (g' t) t := fun t ht =>
    ((hf t ht).differentiableAt.hasDerivAt).comp t (hasDerivAt_vertical σ t)
  have hcont : ContinuousOn g' (Icc T₁ T₂) := by
    intro t ht
    have hd : ContinuousAt (deriv f) (σ + t * I) := (hf t ht).deriv.continuousAt
    have hp : ContinuousAt (fun t : ℝ => (σ : ℂ) + t * I) t := by fun_prop
    exact ((hd.comp (f := fun t : ℝ => (σ : ℂ) + t * I) hp).mul continuousAt_const).continuousWithinAt
  have key := abs_im_integral_logDeriv_le_pi h12 hderiv hcont hre
  have e : (fun t => g' t / g t) = fun t : ℝ => logDeriv f (σ + t * I) * I := by
    funext t
    simp only [hg, hg', logDeriv_apply]
    ring
  rw [e] at key
  exact key

/-- **(A), horizontal segment**: f analytic with Re f > 0 along [a,b] + iT ⇒ |Im ∫ f′/f(σ+iT) dσ| ≤ π. -/
theorem abs_im_integral_logDeriv_horizontal_le_pi {f : ℂ → ℂ} {T a b : ℝ} (hab : a ≤ b)
    (hf : ∀ σ ∈ Icc a b, AnalyticAt ℂ f (σ + T * I))
    (hre : ∀ σ ∈ Icc a b, 0 < (f (σ + T * I)).re) :
    |(∫ σ in a..b, logDeriv f (σ + T * I)).im| ≤ Real.pi := by
  set g : ℝ → ℂ := fun σ => f (σ + T * I) with hg
  set g' : ℝ → ℂ := fun σ => deriv f (σ + T * I) with hg'
  have hderiv : ∀ σ ∈ Icc a b, HasDerivAt g (g' σ) σ := fun σ hσ => by
    have := ((hf σ hσ).differentiableAt.hasDerivAt).comp σ (hasDerivAt_horizontal T σ)
    exact this.congr_deriv (mul_one _)
  have hcont : ContinuousOn g' (Icc a b) := by
    intro σ hσ
    have hd : ContinuousAt (deriv f) (σ + T * I) := (hf σ hσ).deriv.continuousAt
    have hp : ContinuousAt (fun σ : ℝ => (σ : ℂ) + T * I) σ := by fun_prop
    exact (hd.comp (f := fun σ : ℝ => (σ : ℂ) + T * I) hp).continuousWithinAt
  have key := abs_im_integral_logDeriv_le_pi hab hderiv hcont hre
  have e : (fun σ => g' σ / g σ) = fun σ : ℝ => logDeriv f (σ + T * I) := by
    funext σ
    simp only [hg, hg', logDeriv_apply]
  rw [e] at key
  exact key

/-! ### (B) one partial-fraction term -/

lemma continuousOn_inv_sub {a b T : ℝ} {ρ : ℂ} (hρ : ∀ σ ∈ uIcc a b, (σ : ℂ) + T * I ≠ ρ) :
    ContinuousOn (fun σ : ℝ => ((σ : ℂ) + T * I - ρ)⁻¹) (uIcc a b) := by
  apply ContinuousOn.inv₀ (by fun_prop)
  intro σ hσ
  exact sub_ne_zero.mpr (hρ σ hσ)

theorem intervalIntegrable_inv_sub {a b T : ℝ} {ρ : ℂ} (hρ : ∀ σ ∈ uIcc a b, (σ : ℂ) + T * I ≠ ρ) :
    IntervalIntegrable (fun σ : ℝ => ((σ : ℂ) + T * I - ρ)⁻¹) volume a b :=
  (continuousOn_inv_sub hρ).intervalIntegrable

/-- **(B)** |Im ∫_a^b dσ/(σ + iT − ρ)| ≤ π whenever ρ is not on the segment. -/
theorem abs_im_integral_inv_sub_le_pi {a b : ℝ} (hab : a ≤ b) (T : ℝ) (ρ : ℂ)
    (hρ : ∀ σ ∈ Icc a b, (σ : ℂ) + T * I ≠ ρ) :
    |(∫ σ in a..b, ((σ : ℂ) + T * I - ρ)⁻¹).im| ≤ Real.pi := by
  have hρ' : ∀ σ ∈ uIcc a b, (σ : ℂ) + T * I ≠ ρ := by rw [uIcc_of_le hab]; exact hρ
  rcases eq_or_ne (T - ρ.im) 0 with h0 | h0
  · -- the integrand is real: Im = 0 pointwise
    have him : ∀ σ : ℝ, (((σ : ℂ) + T * I - ρ)⁻¹).im = 0 := by
      intro σ
      rw [Complex.inv_im]
      simp [show T = ρ.im by linarith]
    have hcont := continuousOn_inv_sub hρ'
    have e : (∫ σ in a..b, ((σ : ℂ) + T * I - ρ)⁻¹).im
        = ∫ σ in a..b, (((σ : ℂ) + T * I - ρ)⁻¹).im :=
      (Complex.imCLM.intervalIntegral_comp_comm hcont.intervalIntegrable).symm
    rw [e]
    simp only [him]
    rw [intervalIntegral.integral_zero, abs_zero]
    exact Real.pi_pos.le
  · -- Im(σ + iT − ρ) = T − Im ρ ≠ 0: the segment misses the real axis, log is a primitive
    set c : ℂ := T * I - ρ with hc
    have hcim : c.im = T - ρ.im := by simp [hc]
    have hslit : ∀ σ : ℝ, (σ : ℂ) + c ∈ Complex.slitPlane := by
      intro σ
      rw [Complex.mem_slitPlane_iff]
      right
      simp [hcim, h0]
    have hderiv : ∀ σ : ℝ, HasDerivAt (fun σ : ℝ => Complex.log ((σ : ℂ) + c)) (((σ : ℂ) + c)⁻¹) σ := by
      intro σ
      have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) + c) 1 σ := by
        have := (Complex.ofRealCLM.hasDerivAt (x := σ)).add_const c
        simpa using this
      have h2 : HasDerivAt Complex.log ((σ : ℂ) + c)⁻¹ ((σ : ℂ) + c) := Complex.hasDerivAt_log (hslit σ)
      exact (h2.comp σ h1).congr_deriv (mul_one _)
    have e : (fun σ : ℝ => ((σ : ℂ) + T * I - ρ)⁻¹) = fun σ : ℝ => ((σ : ℂ) + c)⁻¹ := by
      funext σ; simp [hc, sub_eq_add_neg, add_assoc]
    rw [e]
    have hint : IntervalIntegrable (fun σ : ℝ => ((σ : ℂ) + c)⁻¹) volume a b := by
      rw [← e]; exact intervalIntegrable_inv_sub hρ'
    rw [integral_eq_sub_of_hasDerivAt (fun σ _ => hderiv σ) hint, Complex.sub_im, Complex.log_im,
      Complex.log_im]
    -- both arguments lie in the same open half (sign of c.im)
    have hbim : ((b : ℂ) + c).im = c.im := by simp
    have haim : ((a : ℂ) + c).im = c.im := by simp
    rcases lt_or_gt_of_ne h0 with hneg | hpos
    · have hcneg : c.im < 0 := by rw [hcim]; exact hneg
      have h1 : Complex.arg ((b : ℂ) + c) < 0 := Complex.arg_neg_iff.mpr (by rw [hbim]; exact hcneg)
      have h2 : Complex.arg ((a : ℂ) + c) < 0 := Complex.arg_neg_iff.mpr (by rw [haim]; exact hcneg)
      have h3 := Complex.neg_pi_lt_arg ((b : ℂ) + c)
      have h4 := Complex.neg_pi_lt_arg ((a : ℂ) + c)
      rw [abs_le]; constructor <;> linarith
    · have hcpos : 0 < c.im := by rw [hcim]; exact hpos
      have h1 : 0 ≤ Complex.arg ((b : ℂ) + c) := Complex.arg_nonneg_iff.mpr (by rw [hbim]; exact hcpos.le)
      have h2 : 0 ≤ Complex.arg ((a : ℂ) + c) := Complex.arg_nonneg_iff.mpr (by rw [haim]; exact hcpos.le)
      have h3 := Complex.arg_le_pi ((b : ℂ) + c)
      have h4 := Complex.arg_le_pi ((a : ℂ) + c)
      rw [abs_le]; constructor <;> linarith

end ZeroCount
end XiPrime
end Zeta23
