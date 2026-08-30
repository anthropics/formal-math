/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — Taper/Strip.lean.
[eq:hfbound] specialized to `f = φ`, `Λ_f = L/2` (as consumed by [prop:tail]):
"`|φ̂(r − iy)| ≤ e^{L/4} ‖φ''‖₁ |r − iy|⁻²`" for `|y| ≤ 1/2`.
All three statements are proved here from the general-`f` bounds in Zeta23/Poisson/PaperFT.lean,
and are consumed via `Zeta23.Params.norm_phiHat_*`.
Reference: the paper, §2.1 [eq:hfbound], §4 [prop:tail].
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Zeta23.Taper.Basic

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform

namespace Zeta23

namespace Taper

section HfPhi
variable {ϱ : ℝ → ℝ} {L w : ℝ}

/-- `u ↦ (φ u : ℂ)` is `C³`. -/
theorem phiC_contDiff (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ContDiff ℝ 3 (fun u => (phi ϱ L w u : ℂ)) :=
  ofRealCLM.contDiff.comp (phi_contDiff hϱ hw hwL)

theorem phiC_support (hϱ : TaperProfile ϱ) (hw : 0 < w) :
    ∀ u, (phi ϱ L w u : ℂ) ≠ 0 → |u| ≤ L / 2 := by
  intro u hu
  by_contra h
  exact hu (by rw [phi_eq_zero hϱ hw (le_of_lt (not_le.mp h)), ofReal_zero])

/-- `deriv` commutes with the coercion `ℝ → ℂ` for differentiable functions. -/
theorem deriv_ofReal_comp {f : ℝ → ℝ} (hf : Differentiable ℝ f) :
    deriv (fun u => (f u : ℂ)) = fun u => ((deriv f u : ℝ) : ℂ) := by
  funext u
  exact ((hf u).hasDerivAt.ofReal_comp).deriv

theorem deriv_deriv_phiC (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    deriv (deriv (fun u => (phi ϱ L w u : ℂ)))
      = fun u => ((deriv (deriv (phi ϱ L w)) u : ℝ) : ℂ) := by
  have h3 := phi_contDiff hϱ hw hwL
  have hd1 : Differentiable ℝ (phi ϱ L w) := h3.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (deriv (phi ϱ L w)) :=
    (h3.deriv' (n := 2)).differentiable (by norm_num)
  rw [deriv_ofReal_comp hd1, deriv_ofReal_comp hd2]

/-- [eq:hfbound] for φ: `‖φ̂(z)‖ · ‖z‖² ≤ e^{|Im z|·L/2} · C₁` for all complex `z`,
`C₁ = ‖φ''‖₁`. -/
theorem norm_phiHat_mul_sq_le (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (z : ℂ) :
    ‖phiHat ϱ L w z‖ * ‖z‖ ^ 2 ≤ Real.exp (|z.im| * (L / 2)) * C1 ϱ L w := by
  have h := norm_paperFT_mul_sq_le ((phiC_contDiff hϱ hw hwL).of_le (by norm_num))
    (phiC_support hϱ hw) z
  rw [deriv_deriv_phiC hϱ hw hwL] at h
  simp only [Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- `∫ φ ≤ L` (since `0 ≤ φ ≤ 1` and `supp φ ⊆ [−L/2, L/2]`). -/
theorem integral_phi_le (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ∫ u, phi ϱ L w u ≤ L := by
  have hL : 0 ≤ L := by linarith
  have hle : ∀ u, phi ϱ L w u ≤ (Icc (-(L / 2)) (L / 2)).indicator (fun _ => (1 : ℝ)) u := by
    intro u
    by_cases hu : u ∈ Icc (-(L / 2)) (L / 2)
    · rw [indicator_of_mem hu]; exact phi_le_one hϱ u
    · rw [indicator_of_notMem hu]
      have : u ∉ Function.support (phi ϱ L w) := fun h => hu (phi_support_subset hϱ hw h)
      rw [Function.notMem_support] at this
      rw [this]
  calc ∫ u, phi ϱ L w u ≤ ∫ u, (Icc (-(L / 2)) (L / 2)).indicator (fun _ => (1 : ℝ)) u := by
        apply integral_mono (phi_integrable hϱ hw hwL) _ hle
        exact (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))
    _ = L := by
        rw [integral_indicator_const _ measurableSet_Icc, measureReal_def, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith), smul_eq_mul, mul_one]
        ring

/-- [eq:hfbound] for φ, 0-th order: `‖φ̂(z)‖ ≤ e^{|Im z|·L/2} · ‖φ‖₁ ≤ e^{|Im z| L/2} · L`. -/
theorem norm_phiHat_le (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (z : ℂ) :
    ‖phiHat ϱ L w z‖ ≤ Real.exp (|z.im| * (L / 2)) * L := by
  have hint : Integrable (fun u => (phi ϱ L w u : ℂ)) := (phi_integrable hϱ hw hwL).ofReal
  have h := norm_paperFT_le hint (phiC_support hϱ hw) z
  simp only [Complex.norm_real, Real.norm_eq_abs] at h
  refine le_trans h ?_
  gcongr
  calc ∫ u, |phi ϱ L w u| = ∫ u, phi ϱ L w u := by
        congr 1 with u; exact abs_of_nonneg (phi_nonneg hϱ u)
    _ ≤ L := integral_phi_le hϱ hw hwL

/-- The form used in [prop:tail]: for real `r` and `|y| ≤ 1/2`, `z := r − iy ≠ 0`,
`‖φ̂(r − iy)‖ ≤ e^{L/4} C₁ / ‖r − iy‖²`. -/
theorem norm_phiHat_sub_I_mul_le (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L)
    (r y : ℝ) (hy : |y| ≤ 1 / 2) (hz : (r : ℂ) - I * y ≠ 0) :
    ‖phiHat ϱ L w (r - I * y)‖ ≤ Real.exp (L / 4) * C1 ϱ L w / ‖(r : ℂ) - I * y‖ ^ 2 := by
  have hL : 0 ≤ L := by linarith
  have hC1 : 0 ≤ C1 ϱ L w := integral_nonneg (fun _ => abs_nonneg _)
  rw [le_div_iff₀ (by positivity)]
  refine le_trans (norm_phiHat_mul_sq_le hϱ hw hwL _) ?_
  gcongr
  have him : ((r : ℂ) - I * y).im = -y := by simp
  rw [him, abs_neg]
  nlinarith

end HfPhi

end Taper

end Zeta23
