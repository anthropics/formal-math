/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Window/FlatAdm.lean — the tree's own ramp taper P.phi is an admissible window
(Zeta23.AdmWindow, Zeta23/ThmD/WindowCore.lean) with c = c_ϱ.

WindowCore's header asserts this ("so is the flat window with c = cRho ϱ"); since the
coefficient-generalised prime side is stated over AdmWindow uniformly (one code path for the flat and the
quartic windows), we record it as a lemma.  Every field is a Taper/ fact: [eq:phinorms] ‖φ′‖₁ = ‖(φ²)′‖₁ = 2,
‖φ″‖₁ = 2‖ϱ″‖₁/w ≤ c_ϱ/w, ‖(φ²)″‖₁ ≤ c_ϱ/w (Zeta23/Taper/Norms.lean).
Also: 1/2 ≤ bv (indeed 3/4 ≤ b, Zeta23/Taper/Params.lean three_quarters_le_b); the rfl-bridge
AdmWindow.localFun (P.phi T) (P.L T) = P.localFun T is Zeta23/ThmD/ParamsD.lean's localFun_eq_admWindow.
-/
import Zeta23.ThmD.WindowCore
import Zeta23.Taper
import Zeta23.Assembly

open Set Filter

noncomputable section

namespace Zeta23
namespace XiPrime

/-- the ramp taper φ = ϱ((L/2 − |u|)/w) is an AdmWindow with constant c_ϱ (generic parameters). -/
theorem admWindow_taperPhi {ϱ : ℝ → ℝ} {L w : ℝ} (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    AdmWindow (Taper.phi ϱ L w) L w (Taper.cRho ϱ) where
  one_le_w := hw
  w8 := hwL
  four_le_c := Taper.four_le_cRho hϱ
  even := Taper.phi_even
  nonneg := Taper.phi_nonneg hϱ
  le_one := Taper.phi_le_one hϱ
  contDiff := (Taper.phi_contDiff hϱ (by linarith) (by linarith)).of_le (by norm_num)
  support := fun _ hu => Taper.phi_eq_zero hϱ (by linarith) hu
  l1_deriv := (Taper.integral_abs_deriv_phi hϱ (by linarith) (by linarith)).le
  l1_deriv_sq := (Taper.integral_abs_deriv_phi_sq hϱ (by linarith) (by linarith)).le
  l1_deriv2 := by
    rw [Taper.integral_abs_deriv2_phi hϱ (by linarith) (by linarith)]
    exact div_le_div_of_nonneg_right (Taper.two_mul_l1Deriv2_le_cRho hϱ) (by linarith)
  l1_deriv2_sq := Taper.integral_abs_deriv2_phi_sq_le hϱ hw (by linarith)

/-- **the flat taper of a valid parameter set is an admissible window** (eventually 8w ≤ L). -/
theorem admWindow_taper {P : Params} (hP : P.Valid) {T : ℝ} (hwL : 8 * P.w ≤ P.L T) :
    AdmWindow (P.phi T) (P.L T) P.w P.crho := by
  rw [Params.crho_eq]
  exact admWindow_taperPhi hP.taper hP.one_le_w hwL

/- the abstract local data of the taper ARE P's, field by field: Zeta23/ThmD/ParamsD.lean
`localFun_eq_admWindow (Q : Params) (T) : Q.localFun T = AdmWindow.localFun (Q.phi T) (Q.L T) := rfl`. -/

theorem av_taper (P : Params) (T : ℝ) : AdmWindow.av (P.phi T) (P.L T) = P.a T := rfl
theorem bv_taper (P : Params) (T : ℝ) : AdmWindow.bv (P.phi T) (P.L T) = P.b T := rfl
theorem gv_taper (P : Params) (T : ℝ) : AdmWindow.gv (P.phi T) = P.g T := rfl

/-- 1/2 ≤ bv for the taper (in fact 3/4 ≤ b). -/
theorem half_le_bv_taper {P : Params} (hP : P.Valid) {T : ℝ} (hwL : 8 * P.w ≤ P.L T) :
    1 / 2 ≤ AdmWindow.bv (P.phi T) (P.L T) := by
  rw [bv_taper]; linarith [Params.three_quarters_le_b hP hwL]

/-- **The flat admissible family**, in the `AdmFamily` shape:
∃ T₀, ∀ T ≥ T₀, AdmWindow (P.phi T) (P.L T) P.w c_ϱ ∧ 1/2 ≤ bv. -/
theorem admFamily_taper {P : Params} (hP : P.Valid) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, AdmWindow (P.phi T) (P.L T) P.w P.crho ∧
      1 / 2 ≤ AdmWindow.bv (P.phi T) (P.L T) := by
  have hev : ∀ᶠ T in atTop, 8 * P.w ≤ P.L T :=
    (Assembly.tendsto_L_atTop P hP.lam_pos).eventually_ge_atTop _
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp hev
  exact ⟨T₀, fun T hT => ⟨admWindow_taper hP (hT₀ T hT), half_le_bv_taper hP (hT₀ T hT)⟩⟩

end XiPrime
end Zeta23
