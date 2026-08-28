/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
The paper's Fourier convention and the bound [eq:hfbound].

Reference: the paper, §2.1 [subsec:weil].
-/
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Zeta23.Defs

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform

namespace Zeta23

/-! `Zeta23.paperFT (f : ℝ → ℂ) (z : ℂ) : ℂ := ∫ u, f u * cexp (I * z * u)` is defined in
`Zeta23/Defs.lean`: the paper's convention [subsec:weil] "h_f(z) := f̂(z) = ∫ f(u) e^{izu} du",
sign `+i`, no `2π`, complex argument.  This file supplies the dictionary to Mathlib's `𝓕`
(`∫ f(v) e^{-2πi v w} dv`) and the decay bound [eq:hfbound]. -/

theorem paperFT_def (f : ℝ → ℂ) (z : ℂ) : paperFT f z = ∫ u : ℝ, f u * cexp (I * z * u) := rfl

/-! Mathlib's `integral_const_mul` / `integral_mul_const` are stated for a general `RCLike L`,
and their instance path (RCLike-derived `NormedAddCommGroup ℂ`) does not match the
directly-synthesized `Complex.instNormedAddCommGroup` under `rw`'s reducible unification.
These ℂ-specialized restatements (same proofs) rewrite reliably. -/

theorem integral_const_mul_C (r : ℂ) (f : ℝ → ℂ) : (∫ a, r * f a) = r * ∫ a, f a :=
  integral_const_mul r f

theorem integral_mul_const_C (r : ℂ) (f : ℝ → ℂ) : (∫ a, f a * r) = (∫ a, f a) * r :=
  integral_mul_const r f

/-- Convention dictionary: for REAL argument `s`,
`h_f(s) = 𝓕 f (-s / (2π))` where `𝓕` is Mathlib's Fourier transform. -/
theorem paperFT_ofReal_eq_fourier (f : ℝ → ℂ) (s : ℝ) :
    paperFT f s = 𝓕 f (-s / (2 * π)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold paperFT
  congr 1 with u
  rw [smul_eq_mul, mul_comm (f u)]
  congr 1
  congr 1
  push_cast
  field_simp

/-- Equivalent form of the dictionary: `𝓕 f w = h_f(-2π w)`. -/
theorem fourier_eq_paperFT (f : ℝ → ℂ) (w : ℝ) :
    𝓕 f w = paperFT f (-(2 * π * w)) := by
  have := paperFT_ofReal_eq_fourier f (-(2 * π * w))
  push_cast at this ⊢
  rw [this]
  field_simp

/-! ### [eq:hfbound]

"`|h_f(x+iy)| ≤ e^{|y|Λ_f} min(‖f‖₁, ‖f''‖₁ |x+iy|⁻²)`, `supp f ⊂ [−Λ_f, Λ_f]`, by two integrations
by parts (`h_f(z) = (iz)⁻² ∫ f''(u) e^{izu} du` and `|e^{izu}| = e^{−yu} ≤ e^{|y|Λ_f}` on
`supp f`)."  We prove the two bounds separately, in multiplied-out form. -/

theorem norm_cexp_I_mul (z : ℂ) (u : ℝ) : ‖cexp (I * z * u)‖ = Real.exp (-(z.im * u)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem norm_cexp_I_mul_le {z : ℂ} {u Λ : ℝ} (hu : |u| ≤ Λ) :
    ‖cexp (I * z * u)‖ ≤ Real.exp (|z.im| * Λ) := by
  rw [norm_cexp_I_mul, Real.exp_le_exp]
  calc -(z.im * u) ≤ |z.im * u| := neg_le_abs _
    _ = |z.im| * |u| := abs_mul _ _
    _ ≤ |z.im| * Λ := by gcongr

/-- [eq:hfbound], zeroth order: `supp f ⊆ [−Λ, Λ]` ⇒ `‖h_f(z)‖ ≤ e^{|Im z| Λ} ‖f‖₁`. -/
theorem norm_paperFT_le {f : ℝ → ℂ} {Λ : ℝ} (hfi : Integrable f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ) (z : ℂ) :
    ‖paperFT f z‖ ≤ Real.exp (|z.im| * Λ) * ∫ u, ‖f u‖ := by
  rw [paperFT_def, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hfi.norm.const_mul _) (Eventually.of_forall fun u => ?_)
  rw [norm_mul]
  by_cases hu : f u = 0
  · simp [hu]
  · rw [mul_comm]
    gcongr
    exact norm_cexp_I_mul_le (hsupp u hu)

/-- One integration by parts: `(f')^(z) = −iz · f̂(z)` for `f ∈ C_c¹`. -/
theorem paperFT_deriv {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) (hsupp : HasCompactSupport f) (z : ℂ) :
    paperFT (deriv f) z = -(I * z) * paperFT f z := by
  have hf' : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hfd : ∀ x, HasDerivAt f (deriv f x) x := fun x => (hf.differentiable (by norm_num) x).hasDerivAt
  have hv : ∀ x : ℝ, HasDerivAt (fun u : ℝ => cexp (I * z * u)) (I * z * cexp (I * z * x)) x := by
    intro x
    have h1 : HasDerivAt (fun u : ℝ => I * z * u) (I * z * 1) x :=
      ((hasDerivAt_id x).ofReal_comp).const_mul (I * z)
    simpa [mul_comm] using h1.cexp
  have hcv : Continuous (fun u : ℝ => cexp (I * z * u)) := by fun_prop
  have hcv' : Continuous (fun u : ℝ => I * z * cexp (I * z * u)) := by fun_prop
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable (u := f)
    (v := fun u : ℝ => cexp (I * z * u)) (u' := deriv f)
    (v' := fun x : ℝ => I * z * cexp (I * z * x))
    (fun x _ => hfd x) (fun x _ => hv x)
    ((hf.continuous.mul hcv').integrable_of_hasCompactSupport hsupp.mul_right)
    ((hf'.mul hcv).integrable_of_hasCompactSupport hsupp.deriv.mul_right)
    ((hf.continuous.mul hcv).integrable_of_hasCompactSupport hsupp.mul_right)
  have : (fun u : ℝ => f u * (I * z * cexp (I * z * u))) = fun u => (I * z) * (f u * cexp (I * z * u)) := by
    funext u; ring
  rw [this, integral_const_mul] at key
  have key' : I * z * paperFT f z = -paperFT (deriv f) z := by
    rw [paperFT_def, paperFT_def]; exact key
  linear_combination key'

/-- Two integrations by parts: `(f'')^(z) = −z² · f̂(z)`, i.e. "`h_f(z) = (iz)⁻² ∫ f''(u)e^{izu} du`". -/
theorem paperFT_deriv_deriv {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hsupp : HasCompactSupport f)
    (z : ℂ) : paperFT (deriv (deriv f)) z = -z ^ 2 * paperFT f z := by
  have h1 : ContDiff ℝ 1 (deriv f) := hf.deriv'
  rw [paperFT_deriv h1 hsupp.deriv, paperFT_deriv (hf.of_le (by norm_num)) hsupp]
  ring_nf
  rw [I_sq]
  ring

theorem hasCompactSupport_of_support_subset_abs {E : Type*} [Zero E] {f : ℝ → E} {Λ : ℝ}
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ) : HasCompactSupport f := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -Λ) (b := Λ)) ?_
  intro u hu
  exact abs_le.mp (hsupp u hu)

theorem tsupport_subset_of_support_subset_abs {E : Type*} [Zero E] {f : ℝ → E} {Λ : ℝ}
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ) : tsupport f ⊆ Icc (-Λ) Λ :=
  closure_minimal (fun u hu => abs_le.mp (hsupp u hu)) isClosed_Icc

/-- [eq:hfbound], second order: `supp f ⊆ [−Λ, Λ]`, `f ∈ C²` ⇒
`‖h_f(z)‖ · ‖z‖² ≤ e^{|Im z| Λ} ‖f''‖₁`. -/
theorem norm_paperFT_mul_sq_le {f : ℝ → ℂ} {Λ : ℝ} (hf : ContDiff ℝ 2 f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ) (z : ℂ) :
    ‖paperFT f z‖ * ‖z‖ ^ 2 ≤ Real.exp (|z.im| * Λ) * ∫ u, ‖deriv (deriv f) u‖ := by
  have hcs : HasCompactSupport f := hasCompactSupport_of_support_subset_abs hsupp
  have hts := tsupport_subset_of_support_subset_abs hsupp
  have hsupp2 : ∀ u, deriv (deriv f) u ≠ 0 → |u| ≤ Λ := by
    intro u hu
    have : u ∈ tsupport f :=
      tsupport_deriv_subset (support_deriv_subset (Function.mem_support.mpr hu))
    exact abs_le.mpr (hts this)
  have hint : Integrable (deriv (deriv f)) :=
    (hf.deriv'.continuous_deriv le_rfl).integrable_of_hasCompactSupport hcs.deriv.deriv
  have := norm_paperFT_le hint hsupp2 z
  rw [paperFT_deriv_deriv hf hcs, norm_mul, norm_neg, norm_pow, mul_comm] at this
  exact this

/-- [eq:hfbound] in the paper's form for `z ≠ 0`: `‖h_f(z)‖ ≤ e^{|Im z|Λ} ‖f''‖₁ / ‖z‖²`. -/
theorem norm_paperFT_le_div {f : ℝ → ℂ} {Λ : ℝ} (hf : ContDiff ℝ 2 f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ) {z : ℂ} (hz : z ≠ 0) :
    ‖paperFT f z‖ ≤ Real.exp (|z.im| * Λ) * (∫ u, ‖deriv (deriv f) u‖) / ‖z‖ ^ 2 := by
  rw [le_div_iff₀ (by positivity)]
  exact norm_paperFT_mul_sq_le hf hsupp z

end Zeta23
