/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmD/BridgeD.lean — the Montgomery–Taylor window is an admissible window:
`AdmWindow (phiD ϱ λ L w) L w (cDT ϱ λ)`, using the estimates of Zeta23/ThmD/Window.lean;
the §5 local hypotheses for the D-data then come from Zeta23/ThmD/WindowCore.lean.
-/
import Zeta23.ThmD.WindowLocalHyps
import Zeta23.ThmD.Window
import Zeta23.PrimeSideB.Concrete

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace Zeta23
namespace ThmD

variable {ϱ : ℝ → ℝ} {lam L w : ℝ}

lemma four_le_cDT (hϱ : TaperProfile ϱ) (lam : ℝ) : 4 ≤ cDT ϱ lam := by
  unfold cDT
  have h := Taper.four_le_cRho hϱ
  nlinarith [sq_nonneg lam]

/-- **The Montgomery–Taylor window is admissible** (paper §7.1, sentence 1: even, C_c²,
same support, ‖φ_D'‖₁, ‖(φ_D²)'‖₁ ≤ 2, second-derivative norms ≪ 1/w). -/
theorem admWindow_phiD (hϱ : TaperProfile ϱ) (h0 : 0 < lam) (h1 : lam ≤ 1) (hw : 1 ≤ w)
    (hwL : 8 * w ≤ L) : AdmWindow (phiD ϱ lam L w) L w (cDT ϱ lam) where
  one_le_w := hw
  w8 := hwL
  four_le_c := four_le_cDT hϱ lam
  even := phiD_even
  nonneg := phiD_nonneg hϱ
  le_one := phiD_le_one hϱ
  contDiff := phiD_contDiff hϱ h0 h1 (by linarith) (by linarith)
  support := fun _ hu => phiD_eq_zero hϱ (by linarith) hu
  l1_deriv := integral_abs_deriv_phiD_le hϱ h0 h1 (by linarith) (by linarith)
  l1_deriv_sq := integral_abs_deriv_phiD_sq_le hϱ h0 h1 (by linarith) (by linarith)
  l1_deriv2 := integral_abs_deriv2_phiD_le hϱ h0 h1 hw hwL
  l1_deriv2_sq := integral_abs_deriv2_phiD_sq_le hϱ h0 h1 hw hwL

/-! ## Params-level wrappers (the D-analogue of `Params.localFun`) -/

/-- the Montgomery–Taylor window of the parameter set `P` at height `T`. -/
def _root_.Zeta23.Params.phiD (P : Params) (T : ℝ) : ℝ → ℝ := Zeta23.ThmD.phiD P.ϱ P.lam (P.L T) P.w

/-- its abstract local data `(φ̂_D, Φ_D, A_{φ_D}, g_D, a_D, b_D)`. -/
def _root_.Zeta23.Params.localFunD (P : Params) (T : ℝ) : PrimeSide.LocalFun :=
  AdmWindow.localFun (P.phiD T) (P.L T)

theorem admWindow_params {P : Params} (hP : P.Valid) {T : ℝ} (hwL : 8 * P.w ≤ P.L T) :
    AdmWindow (P.phiD T) (P.L T) P.w (cDT P.ϱ P.lam) :=
  admWindow_phiD hP.taper hP.lam_pos hP.lam_le_one hP.one_le_w hwL

/-! ## `b_D ≥ 1/2` for large `L/w`, and the eventual `LocalHypsCore` for the D-data -/

/-- `b* = 1/2 + sin(2ϑ)/(4ϑ) ≥ 1/2 + 1/π` (Jordan's inequality; `2ϑ = √2 λ ≤ √2 < π/2`). -/
lemma bStar_ge (h0 : 0 < lam) (h1 : lam ≤ 1) : 1 / 2 + 1 / π ≤ bStar lam := by
  rw [bStar_eq h0]
  have hθ := theta_pos h0
  have hθle : theta lam ≤ (Real.sqrt 2)⁻¹ := theta_le h1 h0.le
  have hs2 : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs2pos : 0 < Real.sqrt 2 := by positivity
  have h2θ : 2 * theta lam ≤ π / 2 := by
    have e : 2 * (Real.sqrt 2)⁻¹ = Real.sqrt 2 := by
      rw [← div_eq_mul_inv, div_eq_iff hs2pos.ne']
      have := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num); nlinarith
    have := Real.pi_gt_three
    nlinarith
  have hsin : 2 / π * (2 * theta lam) ≤ Real.sin (2 * theta lam) :=
    Real.mul_le_sin (by positivity) h2θ
  have hπ := Real.pi_pos
  have e : (1 : ℝ) / π = 2 / π * (2 * theta lam) / (4 * theta lam) := by
    field_simp; ring
  rw [e]
  gcongr

/-- for the Montgomery–Taylor window, `b_D ≥ 1/2` as soon as `L ≥ 4π w` (|b_D − b*| ≤ 4w/L). -/
lemma bv_phiD_ge_half (hϱ : TaperProfile ϱ) (h0 : 0 < lam) (h1 : lam ≤ 1) (hw : 1 ≤ w)
    (hwL : 8 * w ≤ L) (hLw : 4 * π * w ≤ L) :
    1 / 2 ≤ AdmWindow.bv (phiD ϱ lam L w) L := by
  have hL : 0 < L := by linarith
  have h := bD_close hϱ h0 h1 hw hwL
  have hb := bStar_ge h0 h1
  have hπ := Real.pi_pos
  have h4 : 4 * w / L ≤ 1 / π := by
    rw [div_le_div_iff₀ hL hπ]; linarith
  unfold AdmWindow.bv
  linarith [(abs_le.mp h).1]

/-- **The D-analogue of `Bridge.localHypsEventually`:** for all large `T`, the Montgomery–Taylor
data `P.localFunD T` satisfy §5's `LocalHypsCore` with constant `cDT`. -/
theorem localHypsCoreD_eventually {P : Params} (hP : P.Valid) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      PrimeSide.LocalHypsCore (cDT P.ϱ P.lam) (P.toSetting T) (P.localFunD T) := by
  have hl : Tendsto l atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))
  have hL : Tendsto P.L atTop atTop := hl.const_mul_atTop hP.lam_pos
  have hX : ∀ᶠ T in atTop, 1 ≤ P.X T := by
    filter_upwards [hL.eventually_ge_atTop 0] with T h
    simpa [Params.X] using Real.one_le_exp h
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp ((hl.eventually_ge_atTop 1).and
    ((hL.eventually_ge_atTop (8 * P.w)).and ((hL.eventually_ge_atTop (4 * π * P.w)).and hX)))
  refine ⟨T₀, fun T hT => ?_⟩
  obtain ⟨h1, h8, h4π, hX1⟩ := hT₀ T hT
  exact AdmWindow.localHypsCore (P.toSetting T) (admWindow_params hP h8) hP.lam_pos hP.lam_le_one
    h1 hX1 (bv_phiD_ge_half hP.taper hP.lam_pos hP.lam_le_one hP.one_le_w h8 h4π)

end ThmD
end Zeta23

end
