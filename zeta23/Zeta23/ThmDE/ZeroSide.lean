/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmDE/ZeroSide.lean — the zero side for L(s,χ) with the
Montgomery–Taylor window, i.e. for the window-realizing family 'P.atD T' (Zeta23/ThmD/ParamsD.lean).

  * 'eventually_tailPackageD_of_localCount' — prop:tail for 'P.atD T' from an ABSTRACT two-sided
    local count N(t, t+1) ≤ A₀ log(|t|+3) (the χ local count, Zeta23.ThmE.*), rather than from
    'PaperInputs.RvM' as in Zeta23/ThmD/ZeroSideD.lean 'eventually_tailPackageD' (same proof);
  * 'eventually_GzGpDChi' — the H-EF(χ) bridge 'Z.Gz (P.atD T) T = GpChi (P.atD T) κ q c T'
    (ZeroConfig.Gz_eq_GpChi, Zeta23/ThmE/GzGpChi.lean, is generic in the parameter set; the C_c^2
    side conditions for φ_D come from the AdmWindow facts exactly as in ThmD.GzGpD_of);
prop:block needs nothing new: ThmD.eventually_blockInputsD is already generic in Z; the
identification of the χ-traces of 'P.atD T' with the abstract-layer χ-traces of the D-data lives
in Zeta23/ThmDE/Concrete.lean.
-/
import Zeta23.ThmD.ZeroSideD
import Zeta23.ThmE.GzGpChi

noncomputable section

open Filter Complex Real Set MeasureTheory

namespace Zeta23
namespace ThmDE

open ThmD ThmE

variable {P : Params}

/-! ### prop:tail for φ_D from an abstract local count -/

theorem eventually_tailPackageD_of_localCount (Z : ZeroConfig) {P : Params} (hP : P.Valid)
    {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) :
    ∃ θ₀ : ℝ → ℝ, (∀ᶠ T in atTop, Assembly.TailInputs Z (P.atD T) T (θ₀ T)) ∧
      ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1) := by
  refine ⟨fun T => Tail.theta0 A₀ (Real.exp (P.L T / 4) * C1D P T) T, ?_, ?_⟩
  · have hL2 : ∀ᶠ T in atTop, 2 ≤ P.L T := (tendsto_L hP).eventually_ge_atTop 2
    filter_upwards [eventually_ge_atTop Tail.T₀, hL2, eventually_w8 hP, eventually_w4pi hP]
      with T hT hL h8 h4π
    have HT : Tail.TailHyp Z (P.atD T) T A₀ (C1D P T) :=
      { hT := hT, hL := hL, hA₀ := hA₀, hloc := hloc, hC₁ := C1D_nonneg P T,
        hdecay := fun r y hy hz => hdecayD hP h8 r y hy hz }
    have ha : 0 < (P.atD T).a T := by linarith [(aD_range_of hP h8 h4π).1]
    exact HT.tailInputs ha (fun z => GzGp.phiHat_conj _ T z)
  · exact Tail.eventually_theta0_le P hP hA₀ (C1D P) (C1D_nonneg P) (R := cDT P.ϱ P.lam / 2)
      ((eventually_w8 hP).mono fun T h8 => by linarith [C1D_le hP h8])

/-! ### The H-EF(χ) bridge for φ_D -/

theorem GzGpDChi_of (Z : ZeroConfig) {κ q : ℕ} {c : ℕ → ℂ} (hP : P.Valid)
    (hEF : ExplicitFormulaPaperChi κ q c Z) {T : ℝ} (h8 : 8 * P.w ≤ P.L T) :
    Z.Gz (P.atD T) T = GpChi (P.atD T) κ q c T := by
  have hW := admWindow_params hP h8
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  refine Z.Gz_eq_GpChi (P.atD T) κ q c T hEF hL ?_ ?_
  · rw [Params.atD_phi_valid T hP]; exact hW.vC_contDiff
  · rw [Params.atD_phi_valid T hP]
    exact closure_minimal hW.support_subset isClosed_Icc

theorem eventually_GzGpDChi (Z : ZeroConfig) {κ q : ℕ} {c : ℕ → ℂ} {P : Params} (hP : P.Valid)
    (hEF : ExplicitFormulaPaperChi κ q c Z) :
    ∀ᶠ T in atTop, Z.Gz (P.atD T) T = GpChi (P.atD T) κ q c T := by
  filter_upwards [eventually_w8 hP] with T h8
  exact GzGpDChi_of Z hP hEF h8

end ThmDE
end Zeta23

end
