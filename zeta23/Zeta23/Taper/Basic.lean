/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — Taper/Basic.lean.  Definitions of the test family
[subsec:family] for generic parameters (ϱ : ℝ → ℝ) (L w : ℝ), and the basic facts of the sentence
after [eq:phidef].  Bodies are literally those of Zeta23/Defs.lean so that
P.phi T = Taper.phi P.ϱ (P.L T) P.w etc. are rfl (bridges in Zeta23/Taper.lean).

Sub-file map (umbrella = Zeta23/Taper.lean):
  Basic   — defs, support/plateau/evenness/C³
  Norms   — [eq:phinorms], [eq:abdef], c_ϱ, C₁, smoothstep
  Strip   — [eq:hfbound] specialized to φ
  Decay   — [eq:gbounds], [eq:psidef], [eq:psiints]
  Fourier — φ̂, Φ real/even/continuous, [eq:PhigA] facts, Plancherel, [eq:Phi2FT]
  Zeta23/Taper.lean — umbrella + the consumer-facing `Params` layer
-/
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Zeta23.Defs
import Zeta23.Poisson.PaperFT

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform

namespace Zeta23

theorem TaperProfile.nonneg {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ) (x : ℝ) : 0 ≤ ϱ x := by
  rw [← hϱ.eq_zero 0 le_rfl]
  rcases le_total 0 x with h | h
  · exact hϱ.monotone h
  · rw [hϱ.eq_zero x h, hϱ.eq_zero 0 le_rfl]

theorem TaperProfile.le_one {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ) (x : ℝ) : ϱ x ≤ 1 := by
  rw [← hϱ.eq_one 1 le_rfl]
  rcases le_total x 1 with h | h
  · exact hϱ.monotone h
  · rw [hϱ.eq_one x h, hϱ.eq_one 1 le_rfl]

theorem TaperProfile.continuous {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ) : Continuous ϱ :=
  hϱ.contDiff.continuous

namespace Taper

/-! ### Constants depending only on ϱ  [eq:phinorms] -/

/-- `‖ϱ'‖_∞`. -/
noncomputable def supDeriv (ϱ : ℝ → ℝ) : ℝ := ⨆ x : ℝ, |deriv ϱ x|

/-- `‖ϱ''‖₁`. -/
noncomputable def l1Deriv2 (ϱ : ℝ → ℝ) : ℝ := ∫ x : ℝ, |deriv (deriv ϱ) x|

/-- [eq:phinorms]: "`c_ϱ := 4‖ϱ'‖_∞ + 4‖ϱ''‖₁ (≥ 4)`".  Body literally equal to `Params.crho`. -/
noncomputable def cRho (ϱ : ℝ → ℝ) : ℝ :=
  4 * (⨆ x : ℝ, |deriv ϱ x|) + 4 * ∫ x : ℝ, |deriv (deriv ϱ) x|

theorem cRho_eq (ϱ : ℝ → ℝ) : cRho ϱ = 4 * supDeriv ϱ + 4 * l1Deriv2 ϱ := rfl

/-- A concrete admissible profile, witnessing that `TaperProfile` is inhabited: Mathlib's
`Real.smoothTransition` (C^∞, monotone, `0` on `(−∞,0]`, `1` on `[1,∞)`).  Not used by the
paper, which fixes an arbitrary ϱ.  (A polynomial C³ smoothstep `x⁴(35 − 84x + 70x² − 20x³)`
would make the constants `‖ϱ'‖_∞ = 35/16`, `‖ϱ''‖₁ = 35/8` numeric; nothing downstream needs
numeric values, so the library function is used.) -/
noncomputable def smoothstep (x : ℝ) : ℝ := Real.smoothTransition x

/-! ### The taper φ [eq:phidef], a, b [eq:abdef], Φ, g, A_φ [eq:PhigA], ψ [eq:psidef] -/

variable (ϱ : ℝ → ℝ) (L w : ℝ)

/-- [eq:phidef]: "`φ(u) := ϱ((L/2 − |u|)/w)`, `u ∈ ℝ`". -/
noncomputable def phi (u : ℝ) : ℝ := ϱ ((L / 2 - |u|) / w)

/-- [eq:abdef]: "`a := L⁻¹ ∫ φ²`". -/
noncomputable def aConst : ℝ := L⁻¹ * ∫ u : ℝ, (phi ϱ L w u) ^ 2

/-- [eq:abdef]: "`b := L⁻¹ ∫ φ⁴`". -/
noncomputable def bConst : ℝ := L⁻¹ * ∫ u : ℝ, (phi ϱ L w u) ^ 4

/-- `φ̂(z) = h_φ(z) = ∫ φ(u) e^{izu} du` (paper convention, complex argument). -/
noncomputable def phiHat (z : ℂ) : ℂ := paperFT (fun u => (phi ϱ L w u : ℂ)) z

/-- `φ̂` on the real line as a real number. -/
noncomputable def phiHatR (r : ℝ) : ℝ := (phiHat ϱ L w (r : ℂ)).re

/-- [eq:PhigA]: "`Φ := (φ²)^`" (complex argument). -/
noncomputable def Phi (z : ℂ) : ℂ := paperFT (fun u => (((phi ϱ L w u) ^ 2 : ℝ) : ℂ)) z

/-- `Φ` on the real line as a real number. -/
noncomputable def PhiR (r : ℝ) : ℝ := (Phi ϱ L w (r : ℂ)).re

/-- [eq:PhigA]: "`g := φ² ⋆ φ²`", `(v ⋆ v)(y) := ∫ v(u) v(u+y) du`. -/
noncomputable def g (y : ℝ) : ℝ := Params.autocorr (fun u => (phi ϱ L w u) ^ 2) y

/-- [eq:PhigA]: "`A_φ := φ ⋆ φ`". -/
noncomputable def Aphi (y : ℝ) : ℝ := Params.autocorr (phi ϱ L w) y

/-- [eq:psidef]: "`ψ(r) := min(L, 2/|r|, c_ϱ/(w r²))` (`r ∈ ℝ`)".  At `r = 0` the paper's
value is `L` (the other two entries are `+∞`); this is made explicit because Lean's
`2 / 0 = 0`. -/
noncomputable def psi (r : ℝ) : ℝ :=
  if r = 0 then L else min L (min (2 / |r|) (cRho ϱ / (w * r ^ 2)))

/-! ### Basic properties of φ (the sentence after [eq:phidef]):
"`φ ∈ C_c³(ℝ)` is even, `0 ≤ φ ≤ 1`, `supp φ = [−L/2, L/2]`, `φ = 1` on `[−L/2+w, L/2−w]`" -/

section Basic
variable {ϱ L w}

theorem phi_even (u : ℝ) : phi ϱ L w (-u) = phi ϱ L w u := by
  simp [phi, abs_neg]

theorem phi_nonneg (hϱ : TaperProfile ϱ) (u : ℝ) : 0 ≤ phi ϱ L w u := hϱ.nonneg _

theorem phi_le_one (hϱ : TaperProfile ϱ) (u : ℝ) : phi ϱ L w u ≤ 1 := hϱ.le_one _

/-- `φ(u) = 0` for `|u| ≥ L/2`. -/
theorem phi_eq_zero (hϱ : TaperProfile ϱ) (hw : 0 < w) {u : ℝ} (hu : L / 2 ≤ |u|) :
    phi ϱ L w u = 0 := by
  unfold phi
  apply hϱ.eq_zero
  apply div_nonpos_of_nonpos_of_nonneg <;> linarith

/-- `φ = 1` on `[−L/2 + w, L/2 − w]`. -/
theorem phi_eq_one (hϱ : TaperProfile ϱ) (hw : 0 < w) {u : ℝ} (hu : |u| ≤ L / 2 - w) :
    phi ϱ L w u = 1 := by
  unfold phi
  apply hϱ.eq_one
  rw [ge_iff_le, le_div_iff₀ hw]
  linarith

theorem phi_support_subset (hϱ : TaperProfile ϱ) (hw : 0 < w) :
    Function.support (phi ϱ L w) ⊆ Icc (-(L / 2)) (L / 2) := by
  intro u hu
  rw [Function.mem_support] at hu
  by_contra h
  apply hu (phi_eq_zero hϱ hw _)
  rw [mem_Icc, not_and_or, not_le, not_le] at h
  rcases h with h | h
  · exact le_trans (by linarith) (neg_le_abs u)
  · exact le_trans (by linarith) (le_abs_self u)

theorem phi_hasCompactSupport (hϱ : TaperProfile ϱ) (hw : 0 < w) :
    HasCompactSupport (phi ϱ L w) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (phi_support_subset hϱ hw)

/-- Product form of the taper, valid when `2w ≤ L`: `φ(u) = ϱ((L/2−u)/w)·ϱ((L/2+u)/w)`.
(For `u ≥ 0` the second factor is `1` since `(L/2+u)/w ≥ L/(2w) ≥ 1`; symmetrically for
`u ≤ 0`.)  This is how we prove `φ ∈ C³` despite the `|u|` in [eq:phidef]. -/
theorem phi_eq_mul (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (u : ℝ) :
    phi ϱ L w u = ϱ ((L / 2 - u) / w) * ϱ ((L / 2 + u) / w) := by
  unfold phi
  rcases le_total 0 u with h | h
  · rw [abs_of_nonneg h, hϱ.eq_one ((L / 2 + u) / w), mul_one]
    rw [ge_iff_le, le_div_iff₀ hw]; linarith
  · rw [abs_of_nonpos h, hϱ.eq_one ((L / 2 - u) / w), one_mul]
    · ring_nf
    rw [ge_iff_le, le_div_iff₀ hw]; linarith

/-- "`φ ∈ C_c³(ℝ)`". -/
theorem phi_contDiff (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ContDiff ℝ 3 (phi ϱ L w) := by
  have : phi ϱ L w = fun u => ϱ ((L / 2 - u) / w) * ϱ ((L / 2 + u) / w) :=
    funext (phi_eq_mul hϱ hw hwL)
  rw [this]
  apply ContDiff.mul
  · exact hϱ.contDiff.comp (by fun_prop)
  · exact hϱ.contDiff.comp (by fun_prop)

theorem phi_continuous (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Continuous (phi ϱ L w) :=
  (phi_contDiff hϱ hw hwL).continuous

theorem phi_integrable (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Integrable (phi ϱ L w) :=
  (phi_continuous hϱ hw hwL).integrable_of_hasCompactSupport (phi_hasCompactSupport hϱ hw)

end Basic


/-- `C₁ := ‖φ''‖₁` [prop:tail]. -/
noncomputable def C1 (ϱ : ℝ → ℝ) (L w : ℝ) : ℝ := ∫ u, |deriv (deriv (phi ϱ L w)) u|

end Taper

end Zeta23
