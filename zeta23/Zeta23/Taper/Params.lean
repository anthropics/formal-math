/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — Taper/Params.lean.  Consumer-facing layer, part 1:
the `P : Params`, `T : ℝ` versions of everything that depends only on Taper/Basic, Taper/Norms
and Taper/Strip (φ facts [eq:phidef], [eq:abdef], C₁ and [eq:hfbound] for φ), plus the rfl
bridges to Defs.  Split out of Zeta23/Taper.lean so that Zeta23/Main.lean can import it without
pulling Taper/Decay, Taper/Fourier.  Hypotheses: `hP : P.Valid`,
`hwL : 8 * P.w ≤ P.L T` ([eq:wrange]).  The remaining Params-layer facts (φ̂/Φ, ψ, g, A_φ,
Plancherel) are in the umbrella Zeta23/Taper.lean.
-/
import Zeta23.Taper.Basic
import Zeta23.Taper.Norms
import Zeta23.Taper.Strip

open Complex MeasureTheory Real Set Filter Topology

namespace Zeta23

namespace Params

variable (P : Params) (T : ℝ)

theorem phi_eq : P.phi T = Taper.phi P.ϱ (P.L T) P.w := rfl
theorem a_eq : P.a T = Taper.aConst P.ϱ (P.L T) P.w := rfl
theorem b_eq : P.b T = Taper.bConst P.ϱ (P.L T) P.w := rfl
theorem phiHat_eq : P.phiHat T = Taper.phiHat P.ϱ (P.L T) P.w := rfl
theorem phiHatR_eq : P.phiHatR T = Taper.phiHatR P.ϱ (P.L T) P.w := rfl
theorem Phi_eq : P.Phi T = Taper.Phi P.ϱ (P.L T) P.w := rfl
theorem PhiR_eq : P.PhiR T = Taper.PhiR P.ϱ (P.L T) P.w := rfl
theorem g_eq : P.g T = Taper.g P.ϱ (P.L T) P.w := rfl
theorem Aphi_eq : P.Aphi T = Taper.Aphi P.ϱ (P.L T) P.w := rfl
theorem crho_eq : P.crho = Taper.cRho P.ϱ := rfl

/-- ψ (value `L` at `r = 0`); see `Taper.psi`.  Since Defs uses the same body,
`P.psi T = P.psi' T` is `rfl` (`psi_eq_psi'`); both names are available. -/
noncomputable def psi' (r : ℝ) : ℝ := Taper.psi P.ϱ (P.L T) P.w r

theorem psi_eq_psi' : P.psi T = P.psi' T := rfl
theorem psi_eq : P.psi T = Taper.psi P.ϱ (P.L T) P.w := rfl

/-- `C₁ := ‖φ''‖₁` [prop:tail]. -/
noncomputable def C1 : ℝ := Taper.C1 P.ϱ (P.L T) P.w

variable {P T}

theorem w_pos (hP : P.Valid) : 0 < P.w := lt_of_lt_of_le one_pos hP.one_le_w
theorem two_w_le (hwL : 8 * P.w ≤ P.L T) (hP : P.Valid) : 2 * P.w ≤ P.L T := by
  linarith [hP.one_le_w]

/-! #### hypothesis-free facts -/
theorem phi_even' (u : ℝ) : P.phi T (-u) = P.phi T u := Taper.phi_even u

section
variable (hP : P.Valid)
include hP
theorem phi_nonneg (u : ℝ) : 0 ≤ P.phi T u := Taper.phi_nonneg hP.taper u
theorem phi_le_one (u : ℝ) : P.phi T u ≤ 1 := Taper.phi_le_one hP.taper u
theorem phi_eq_zero {u : ℝ} (hu : P.L T / 2 ≤ |u|) : P.phi T u = 0 :=
  Taper.phi_eq_zero hP.taper (w_pos hP) hu
theorem phi_eq_one {u : ℝ} (hu : |u| ≤ P.L T / 2 - P.w) : P.phi T u = 1 :=
  Taper.phi_eq_one hP.taper (w_pos hP) hu
theorem phi_hasCompactSupport : HasCompactSupport (P.phi T) :=
  Taper.phi_hasCompactSupport hP.taper (w_pos hP)
theorem phi_support_subset : Function.support (P.phi T) ⊆ Icc (-(P.L T / 2)) (P.L T / 2) :=
  Taper.phi_support_subset hP.taper (w_pos hP)
end

section
variable (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
include hP hwL

/-! #### φ -/
theorem phi_contDiff : ContDiff ℝ 3 (P.phi T) :=
  Taper.phi_contDiff hP.taper (w_pos hP) (two_w_le hwL hP)
theorem phi_continuous : Continuous (P.phi T) :=
  Taper.phi_continuous hP.taper (w_pos hP) (two_w_le hwL hP)

/-! #### [eq:abdef] -/
theorem b_le_a : P.b T ≤ P.a T := Taper.bConst_le_aConst hP.taper (w_pos hP) (two_w_le hwL hP)
theorem a_le_one : P.a T ≤ 1 := Taper.aConst_le_one hP.taper (w_pos hP) (two_w_le hwL hP)
theorem one_sub_le_b : 1 - 2 * P.w / P.L T ≤ P.b T :=
  Taper.one_sub_le_bConst hP.taper (w_pos hP) (two_w_le hwL hP)
theorem b_nonneg : 0 ≤ P.b T := Taper.bConst_nonneg hP.taper (w_pos hP) (two_w_le hwL hP)
theorem three_quarters_le_b : 3 / 4 ≤ P.b T := by
  have h1 := one_sub_le_b hP hwL
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have : 2 * P.w / P.L T ≤ 1 / 4 := by
    rw [div_le_iff₀ hL]; linarith
  linarith
/-- "and `a ≥ 1/2`" [prop:tail, last line]. -/
theorem half_le_a : 1 / 2 ≤ P.a T := by
  linarith [three_quarters_le_b hP hwL, b_le_a hP hwL]

/-! #### [eq:hfbound] for φ ([prop:tail]) -/
theorem C1_le : P.C1 T ≤ 2 * Taper.l1Deriv2 P.ϱ :=
  Taper.C1_le hP.taper hP.one_le_w (two_w_le hwL hP)
theorem norm_phiHat_mul_sq_le (z : ℂ) :
    ‖P.phiHat T z‖ * ‖z‖ ^ 2 ≤ Real.exp (|z.im| * (P.L T / 2)) * P.C1 T :=
  Taper.norm_phiHat_mul_sq_le hP.taper (w_pos hP) (two_w_le hwL hP) z
theorem norm_phiHat_le (z : ℂ) : ‖P.phiHat T z‖ ≤ Real.exp (|z.im| * (P.L T / 2)) * P.L T :=
  Taper.norm_phiHat_le hP.taper (w_pos hP) (two_w_le hwL hP) z
theorem norm_phiHat_sub_I_mul_le (r y : ℝ) (hy : |y| ≤ 1 / 2) (hz : (r : ℂ) - I * y ≠ 0) :
    ‖P.phiHat T (r - I * y)‖ ≤ Real.exp (P.L T / 4) * P.C1 T / ‖(r : ℂ) - I * y‖ ^ 2 :=
  Taper.norm_phiHat_sub_I_mul_le hP.taper (w_pos hP) (two_w_le hwL hP) r y hy hz

end

end Params

end Zeta23
