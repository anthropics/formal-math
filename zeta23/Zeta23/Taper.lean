/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Taper.lean — the test family [subsec:family] of the paper §2.2 and its
elementary facts: text after [eq:phidef], [eq:phinorms], [eq:abdef], the facts after [eq:PhigA]
(incl. [eq:Phi2FT]), [eq:gbounds], [eq:psidef], [eq:psiints], and [eq:hfbound] specialized to φ.
([eq:hfbound] for general f is in `Zeta23.Poisson.PaperFT`.)

SUB-FILES: Zeta23/Taper/Basic.lean (defs + [eq:phidef] facts),
Norms.lean ([eq:phinorms], [eq:abdef]), Strip.lean ([eq:hfbound] for φ),
Decay.lean ([eq:gbounds], [eq:psidef], [eq:psiints]),
Fourier.lean ([eq:PhigA]-line facts, Plancherel, [eq:Phi2FT]).  This umbrella file
holds the consumer-facing `Params` layer, part 2 (φ̂/Φ/ψ/g/A_φ facts); part 1 (φ, a, b, C₁,
hfbound — depends only on Basic/Norms/Strip) is Zeta23/Taper/Params.lean, importable on its own.

ORGANIZATION.  Namespace `Zeta23.Taper`: generic parameters `(ϱ : ℝ → ℝ) (L w : ℝ)` — pure
one-variable calculus, no `T`.  Namespace `Zeta23.Params` (last section): the same facts for
`P : Params`, `T : ℝ` of Zeta23/Defs.lean (`L = P.L T`, `w = P.w`, `ϱ = P.ϱ`); the bridges
`P.phi T = Taper.phi P.ϱ (P.L T) P.w` etc. are `rfl`.  Consumers use the `Params` versions.

Side conditions: the paper fixes `1 ≤ w ≤ L/8` [eq:wrange].  Generic lemmas carry the minimal
hypothesis they need (`0 < w`, `2w ≤ L`, …); the `Params` versions uniformly assume
`hP : P.Valid` (gives `1 ≤ w`, `TaperProfile ϱ`) and `hwL : 8 * P.w ≤ P.L T` ([eq:wrange]).
-/
import Zeta23.Taper.Params
import Zeta23.Taper.Decay
import Zeta23.Taper.Fourier

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform

namespace Zeta23

/-! ## Instantiation for `P : Params`, `T : ℝ` (Zeta23/Defs.lean).
Consumer-facing names.  Hypotheses: `hP : P.Valid`, `hwL : 8 * P.w ≤ P.L T` ([eq:wrange]). -/

namespace Params

variable {P : Params} {T : ℝ}

/-! #### hypothesis-free facts -/
theorem phiHat_ofReal (r : ℝ) : P.phiHat T r = (P.phiHatR T r : ℂ) := Taper.phiHat_ofReal r
theorem Phi_ofReal (r : ℝ) : P.Phi T r = (P.PhiR T r : ℂ) := Taper.Phi_ofReal r
theorem phiHat_conj (z : ℂ) : P.phiHat T (starRingEnd ℂ z) = starRingEnd ℂ (P.phiHat T z) :=
  Taper.phiHat_conj z
theorem phiHatR_even (r : ℝ) : P.phiHatR T (-r) = P.phiHatR T r := Taper.phiHatR_even r
theorem PhiR_even (r : ℝ) : P.PhiR T (-r) = P.PhiR T r := Taper.PhiR_even r
theorem Aphi_even (y : ℝ) : P.Aphi T (-y) = P.Aphi T y := Taper.Aphi_even y
theorem g_even (y : ℝ) : P.g T (-y) = P.g T y := Taper.g_even y
theorem psi'_even (r : ℝ) : P.psi' T (-r) = P.psi' T r := Taper.psi_even r

section
variable (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
include hP hwL

/-! #### φ̂, Φ real/even/continuous; conj symmetry -/
theorem phiHatR_continuous : Continuous (P.phiHatR T) :=
  Taper.phiHatR_continuous hP.taper (w_pos hP) (two_w_le hwL hP)
theorem PhiR_continuous : Continuous (P.PhiR T) :=
  Taper.PhiR_continuous hP.taper (w_pos hP) (two_w_le hwL hP)
theorem PhiR_contDiff_one : ContDiff ℝ 1 (P.PhiR T) :=
  Taper.PhiR_contDiff_one hP.taper (w_pos hP) (two_w_le hwL hP)

/-! #### [eq:PhigA]-line facts -/
theorem phiHatR_zero_le : P.phiHatR T 0 ≤ P.L T :=
  Taper.phiHatR_zero_le hP.taper (w_pos hP) (two_w_le hwL hP)
theorem PhiR_zero : P.PhiR T 0 = P.a T * P.L T :=
  Taper.PhiR_zero hP.taper (w_pos hP) (two_w_le hwL hP)
theorem g_zero : P.g T 0 = P.b T * P.L T := Taper.g_zero hP.taper (w_pos hP) (two_w_le hwL hP)
theorem Aphi_zero : P.Aphi T 0 = P.a T * P.L T :=
  Taper.Aphi_zero hP.taper (w_pos hP) (two_w_le hwL hP)
theorem phiHatR_sq_eq (r : ℝ) :
    ((P.phiHatR T r) ^ 2 : ℂ) = paperFT (fun u => (P.Aphi T u : ℂ)) r :=
  Taper.phiHatR_sq_eq hP.taper (w_pos hP) (two_w_le hwL hP) r
theorem PhiR_sq_eq (r : ℝ) : ((P.PhiR T r) ^ 2 : ℂ) = paperFT (fun u => (P.g T u : ℂ)) r :=
  Taper.PhiR_sq_eq hP.taper (w_pos hP) (two_w_le hwL hP) r
theorem integral_phiHatR_sq : ∫ r, P.phiHatR T r ^ 2 = 2 * π * P.a T * P.L T :=
  Taper.integral_phiHatR_sq hP.taper (w_pos hP) (two_w_le hwL hP)
theorem integral_PhiR_sq : ∫ r, P.PhiR T r ^ 2 = 2 * π * P.b T * P.L T :=
  Taper.integral_PhiR_sq hP.taper (w_pos hP) (two_w_le hwL hP)
theorem integral_phiHatR_sq_mul_cos (y : ℝ) :
    ∫ r, P.phiHatR T r ^ 2 * Real.cos (r * y) = 2 * π * P.Aphi T y :=
  Taper.integral_phiHatR_sq_mul_cos hP.taper (w_pos hP) (two_w_le hwL hP) y
theorem integral_PhiR_sq_mul_cos (y : ℝ) :
    ∫ x, P.PhiR T x ^ 2 * Real.cos (x * y) = 2 * π * P.g T y :=
  Taper.integral_PhiR_sq_mul_cos hP.taper (w_pos hP) (two_w_le hwL hP) y
theorem integrable_phiHatR_sq : Integrable (fun r => P.phiHatR T r ^ 2) :=
  Taper.integrable_phiHatR_sq hP.taper (w_pos hP) (two_w_le hwL hP)
theorem integrable_phiHatR_sq_mul_abs : Integrable (fun r => P.phiHatR T r ^ 2 * |r|) :=
  Taper.integrable_phiHatR_sq_mul_abs hP.taper (w_pos hP) (two_w_le hwL hP)
theorem integrable_PhiR_sq : Integrable (fun x => P.PhiR T x ^ 2) :=
  Taper.integrable_PhiR_sq hP.taper (w_pos hP) (two_w_le hwL hP)
theorem integrable_PhiR_sq_mul_abs : Integrable (fun x => P.PhiR T x ^ 2 * |x|) :=
  Taper.integrable_PhiR_sq_mul_abs hP.taper (w_pos hP) (two_w_le hwL hP)
theorem integral_phiHatR_sq_mul_abs_le :
    ∫ r, P.phiHatR T r ^ 2 * |r| ≤ 8 + 8 * Real.log (P.crho * P.L T / (4 * P.w)) :=
  Taper.integral_phiHatR_sq_mul_abs_le hP.taper hP.one_le_w hwL
theorem integral_PhiR_sq_mul_abs_le :
    ∫ x, P.PhiR T x ^ 2 * |x| ≤ 8 + 8 * Real.log (P.crho * P.L T / (4 * P.w)) :=
  Taper.integral_PhiR_sq_mul_abs_le hP.taper hP.one_le_w hwL
theorem integrable_phiHatR_sq_mul_sq : Integrable (fun r => P.phiHatR T r ^ 2 * r ^ 2) :=
  Taper.integrable_phiHatR_sq_mul_sq hP.taper hP.one_le_w hwL
theorem integral_phiHatR_sq_mul_sq_le : ∫ r, P.phiHatR T r ^ 2 * r ^ 2 ≤ 8 + 2 * (P.crho / P.w) ^ 2 :=
  Taper.integral_phiHatR_sq_mul_sq_le hP.taper hP.one_le_w hwL
theorem integrable_PhiR_sq_mul_sq : Integrable (fun x => P.PhiR T x ^ 2 * x ^ 2) :=
  Taper.integrable_PhiR_sq_mul_sq hP.taper hP.one_le_w hwL
theorem integral_PhiR_sq_mul_sq_le : ∫ x, P.PhiR T x ^ 2 * x ^ 2 ≤ 8 + 2 * (P.crho / P.w) ^ 2 :=
  Taper.integral_PhiR_sq_mul_sq_le hP.taper hP.one_le_w hwL

/-! #### [eq:gbounds] -/
theorem g_ge (y : ℝ) : max (P.L T - 2 * P.w - |y|) 0 ≤ P.g T y :=
  Taper.g_ge hP.taper (w_pos hP) (two_w_le hwL hP) y
theorem g_le_Aphi (y : ℝ) : P.g T y ≤ P.Aphi T y :=
  Taper.g_le_Aphi hP.taper (w_pos hP) (two_w_le hwL hP) y
theorem Aphi_le (y : ℝ) : P.Aphi T y ≤ max (P.L T - |y|) 0 :=
  Taper.Aphi_le hP.taper (w_pos hP) (two_w_le hwL hP) y
theorem g_nonneg (y : ℝ) : 0 ≤ P.g T y := Taper.g_nonneg hP.taper (w_pos hP) (two_w_le hwL hP) y
theorem Aphi_nonneg (y : ℝ) : 0 ≤ P.Aphi T y :=
  Taper.Aphi_nonneg hP.taper (w_pos hP) (two_w_le hwL hP) y
theorem g_eq_zero {y : ℝ} (hy : P.L T ≤ |y|) : P.g T y = 0 :=
  Taper.g_eq_zero hP.taper (w_pos hP) (two_w_le hwL hP) hy
theorem Aphi_eq_zero {y : ℝ} (hy : P.L T ≤ |y|) : P.Aphi T y = 0 :=
  Taper.Aphi_eq_zero hP.taper (w_pos hP) (two_w_le hwL hP) hy
theorem g_continuous : Continuous (P.g T) :=
  Taper.g_continuous hP.taper (w_pos hP) (two_w_le hwL hP)
theorem Aphi_continuous : Continuous (P.Aphi T) :=
  Taper.Aphi_continuous hP.taper (w_pos hP) (two_w_le hwL hP)

/-! #### [eq:psidef] division-free, and ψ form -/
theorem abs_phiHatR_le_L (r : ℝ) : |P.phiHatR T r| ≤ P.L T :=
  Taper.abs_phiHatR_le_L hP.taper (w_pos hP) (two_w_le hwL hP) r
theorem abs_phiHatR_mul_abs_le (r : ℝ) : |P.phiHatR T r| * |r| ≤ 2 :=
  Taper.abs_phiHatR_mul_abs_le hP.taper (w_pos hP) (two_w_le hwL hP) r
theorem abs_phiHatR_mul_sq_le (r : ℝ) : |P.phiHatR T r| * r ^ 2 ≤ P.crho / P.w :=
  Taper.abs_phiHatR_mul_sq_le hP.taper hP.one_le_w (two_w_le hwL hP) r
theorem abs_PhiR_le_L (r : ℝ) : |P.PhiR T r| ≤ P.L T :=
  Taper.abs_PhiR_le_L hP.taper (w_pos hP) (two_w_le hwL hP) r
theorem abs_PhiR_mul_abs_le (r : ℝ) : |P.PhiR T r| * |r| ≤ 2 :=
  Taper.abs_PhiR_mul_abs_le hP.taper (w_pos hP) (two_w_le hwL hP) r
theorem abs_PhiR_mul_sq_le (r : ℝ) : |P.PhiR T r| * r ^ 2 ≤ P.crho / P.w :=
  Taper.abs_PhiR_mul_sq_le hP.taper hP.one_le_w (two_w_le hwL hP) r
theorem abs_phiHatR_le_psi' (r : ℝ) : |P.phiHatR T r| ≤ P.psi' T r :=
  Taper.abs_phiHatR_le_psi hP.taper hP.one_le_w (two_w_le hwL hP) r
theorem abs_PhiR_le_psi' (r : ℝ) : |P.PhiR T r| ≤ P.psi' T r :=
  Taper.abs_PhiR_le_psi hP.taper hP.one_le_w (two_w_le hwL hP) r
theorem psi'_nonneg (r : ℝ) : 0 ≤ P.psi' T r :=
  Taper.psi_nonneg hP.taper hP.one_le_w (two_w_le hwL hP) r

/-! #### [eq:psiints] -/
theorem integral_psi'_Ioi_le :
    ∫ r in Ioi 0, P.psi' T r ≤ 4 + 2 * Real.log (P.crho * P.L T / (4 * P.w)) :=
  Taper.integral_psi_Ioi_le hP.taper hP.one_le_w hwL
theorem integral_psi'_sq_mul_abs_le :
    ∫ r, P.psi' T r ^ 2 * |r| ≤ 8 + 8 * Real.log (P.crho * P.L T / (4 * P.w)) :=
  Taper.integral_psi_sq_mul_abs_le hP.taper hP.one_le_w hwL
theorem integral_psi'_sq_le : ∫ r, P.psi' T r ^ 2 ≤ 8 * P.L T :=
  Taper.integral_psi_sq_le hP.taper hP.one_le_w hwL
theorem psi'_integrable : Integrable (P.psi' T) := Taper.psi_integrable hP.taper hP.one_le_w hwL
theorem psi'_sq_integrable : Integrable (fun r => P.psi' T r ^ 2) :=
  Taper.psi_sq_integrable hP.taper hP.one_le_w hwL
theorem psi'_sq_mul_abs_integrable : Integrable (fun r => P.psi' T r ^ 2 * |r|) :=
  Taper.psi_sq_mul_abs_integrable hP.taper hP.one_le_w hwL


end

end Params

end Zeta23
