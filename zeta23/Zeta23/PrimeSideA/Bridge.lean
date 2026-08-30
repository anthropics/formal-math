/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
  Part of the Zeta23 formalization of the paper
  "More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/
import Zeta23.PrimeSideB.Concrete
import Zeta23.Taper
import Zeta23.Taper.Norms
import Zeta23.Poisson
import Zeta23.PiFacts

/-!
# Bridge: the concrete taper data satisfy the abstract prime-side hypotheses `LocalHyps`

The §5 layer (`Zeta23/PrimeSideA.lean`) is proved for abstract data
`p : Setting = (T, λ, w)`, `F : LocalFun = (φ̂, Φ, A_φ, g, a, b)` under `LocalHyps cϱ p F` — the list
of test-family facts [eq:psidef], [eq:psiints], [eq:abdef], [eq:gbounds], [eq:PhigA], [eq:Phi2FT],
[lem:poisson], [eq:PiPfacts] used in §5.  Here:

* `localHyps_concrete` — every `LocalHyps` field for the concrete data, from `Taper.lean`,
  `Poisson.lean` ([lem:poisson]) and `PiFacts.lean`, with
  `cϱ := P.crho = c_ϱ` [eq:phinorms]; hence `localHypsEventually : LocalHypsEventually P.crho P`;
(The instantiation `Params.toSetting / localFun` itself lives in `Zeta23/PrimeSideB/Concrete.lean`.)
-/

noncomputable section

open Real Filter Topology MeasureTheory
open scoped BigOperators ArithmeticFunction

namespace Zeta23

namespace PrimeSide

/-! ## The concrete data satisfy `LocalHyps` -/

/-- The guarded majorant `psiA` [eq:psidef] on the concrete data is Taper's `P.psi' T`
(= Defs' `P.psi T`). -/
lemma psiA_concrete (P : Params) (T : ℝ) : psiA P.crho (P.toSetting T) = P.psi' T := by
  funext r; rfl

/-- **All of `LocalHyps` for the concrete taper data**, at any height `T` with `8w ≤ L`
([eq:wrange]), `l ≥ 1` and `X ≥ 1`.  Field-by-field from Taper.lean / Poisson.lean / PiFacts.lean. -/
theorem localHyps_concrete {P : Params} (hP : P.Valid) {T : ℝ} (hwL : 8 * P.w ≤ P.L T)
    (hl : 1 ≤ l T) (hX : 1 ≤ P.X T) : LocalHyps P.crho (P.toSetting T) (P.localFun T) where
  four_le_cϱ := by rw [Params.crho_eq]; exact Taper.four_le_cRho hP.taper
  lam_pos := hP.lam_pos
  lam_le_one := hP.lam_le_one
  one_le_w := hP.one_le_w
  w_le := by show P.w ≤ P.L T / 8; linarith
  one_le_l := hl
  phiHat_cont := Params.phiHatR_continuous hP hwL
  phiHat_even := fun r => Params.phiHatR_even r
  phiHat_le_L := Params.abs_phiHatR_le_L hP hwL
  phiHat_le_inv := Params.abs_phiHatR_mul_abs_le hP hwL
  phiHat_le_sq := Params.abs_phiHatR_mul_sq_le hP hwL
  phiHat_sq_integrable := Params.integrable_phiHatR_sq hP hwL
  phiHat_sq_mul_abs_integrable := Params.integrable_phiHatR_sq_mul_abs hP hwL
  integral_phiHat_sq_mul_abs_le := Params.integral_phiHatR_sq_mul_abs_le hP hwL
  phiHat_sq_mul_sq_integrable := Params.integrable_phiHatR_sq_mul_sq hP hwL
  integral_phiHat_sq_mul_sq_le := Params.integral_phiHatR_sq_mul_sq_le hP hwL
  phiHat_sq_integral := Params.integral_phiHatR_sq hP hwL
  phiHat_sq_fourier := Params.integral_phiHatR_sq_mul_cos hP hwL
  g_lower := Params.g_ge hP hwL
  g_le_Aphi := Params.g_le_Aphi hP hwL
  Aphi_le := Params.Aphi_le hP hwL
  Phi_contDiff := Params.PhiR_contDiff_one hP hwL
  Phi_even := fun r => Params.PhiR_even r
  Phi_le_L := Params.abs_PhiR_le_L hP hwL
  Phi_le_inv := Params.abs_PhiR_mul_abs_le hP hwL
  Phi_le_sq := Params.abs_PhiR_mul_sq_le hP hwL
  Phi_sq_integrable := Params.integrable_PhiR_sq hP hwL
  Phi_sq_mul_abs_integrable := Params.integrable_PhiR_sq_mul_abs hP hwL
  integral_Phi_sq_mul_abs_le := Params.integral_PhiR_sq_mul_abs_le hP hwL
  Phi_sq_mul_sq_integrable := Params.integrable_PhiR_sq_mul_sq hP hwL
  integral_Phi_sq_mul_sq_le := Params.integral_PhiR_sq_mul_sq_le hP hwL
  Phi_zero := Params.PhiR_zero hP hwL
  Phi_sq_integral := Params.integral_PhiR_sq hP hwL
  Phi_sq_fourier := Params.integral_PhiR_sq_mul_cos hP hwL
  poisson := Params.hasSum_phiHatR_mul hP hwL
  b_lower := Params.one_sub_le_b hP hwL
  b_le_a := Params.b_le_a hP hwL
  a_le_one := Params.a_le_one hP hwL
  PiX_cont := PiX_continuous (Real.exp_pos _)
  PiX_bound := PiX_abs_le hX
  psi_integrable := by rw [psiA_concrete]; exact Params.psi'_integrable hP hwL
  psi_sq_integrable := by simpa only [psiA_concrete] using Params.psi'_sq_integrable hP hwL
  integral_psi_Ioi_le := by
    simpa only [psiA_concrete, Params.toSetting_L, Params.toSetting_w] using
      Params.integral_psi'_Ioi_le hP hwL
  integral_psi_sq_le := by
    simpa only [psiA_concrete, Params.toSetting_L] using Params.integral_psi'_sq_le hP hwL
  phiHat_le_psi := by
    simpa only [psiA_concrete, Params.localFun_phiHat] using Params.abs_phiHatR_le_psi' hP hwL
  Phi_le_psi := by
    simpa only [psiA_concrete, Params.localFun_Phi] using Params.abs_PhiR_le_psi' hP hwL

/-- The concrete data satisfy `LocalHyps P.crho` for all large `T`. -/
theorem localHypsEventually {P : Params} (hP : P.Valid) : LocalHypsEventually P.crho P := by
  -- l → ∞, L = λ l → ∞, X = e^L ≥ 1
  have hl : Tendsto l atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))
  have hL : Tendsto P.L atTop atTop := hl.const_mul_atTop hP.lam_pos
  have hX : ∀ᶠ T in atTop, 1 ≤ P.X T := by
    filter_upwards [hL.eventually_ge_atTop 0] with T h
    simpa [Params.X] using Real.one_le_exp h
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp ((hl.eventually_ge_atTop 1).and
    ((hL.eventually_ge_atTop (8 * P.w)).and hX))
  exact ⟨T₀, fun T hT => localHyps_concrete hP (hT₀ T hT).2.1 (hT₀ T hT).1 (hT₀ T hT).2.2⟩

end PrimeSide

end Zeta23

end
