/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmD/ZeroSideD.lean

THE ZERO SIDE FOR THE MONTGOMERY–TAYLOR WINDOW.  The fixed-T zero-side producers
('ZeroSide.blockInputsAt', 'Tail.TailHyp.tailInputs', 'ZeroConfig.Gz_eq_Gp') are generic in the
parameter set, so they apply verbatim to the window-realizing family 'P.atD T' of
Zeta23/ThmD/ParamsD.lean (whose window AT HEIGHT T is φ_D, and whose L, X, d, τ_k are P's by rfl).
The analytic side conditions they ask for (φ̂ real/conj-symmetric, lem:poisson, [eq:hfbound],
φ ∈ C_c^2[−L/2, L/2], 1/2 ≤ a ≤ 1) are supplied for φ_D by Zeta23/ThmD/WindowCore.lean's generic
'AdmWindow' facts via 'ThmD.admWindow_params' (BridgeD.lean).  Exports, all eventually in T:

  * 'eventually_blockInputsD'  — prop:block + [eq:Ncount] for 'P.atD T';
  * 'eventually_tailPackageD'  — prop:tail with θ₀(T) ≤ C·l·T^{λ/2−1};
  * 'eventually_GzGpD'         — the H-EF bridge 'Z.Gz (P.atD T) T = (P.atD T).Gp T';
  * 'eventually_aD_range'      — 1/2 ≤ a_D ≤ 1.
-/
import Zeta23.ThmD.ParamsD
import Zeta23.ZeroSide
import Zeta23.Tail
import Zeta23.Hypotheses.GzGp

noncomputable section

open Filter Complex Real Set MeasureTheory

namespace Zeta23
namespace ThmD

variable {P : Params}

/-! ### Name bridges: the 'Params' Fourier data of 'P.atD T' are the 'AdmWindow' data of φ_D -/

theorem atD_phiHat (hP : P.Valid) (T : ℝ) :
    (P.atD T).phiHat T = AdmWindow.vHat (P.phiD T) := by
  show AdmWindow.vHat ((P.atD T).phi T) = _
  rw [Params.atD_phi_valid T hP]

theorem atD_phiHatR (hP : P.Valid) (T : ℝ) :
    (P.atD T).phiHatR T = AdmWindow.vHatR (P.phiD T) := by
  show AdmWindow.vHatR ((P.atD T).phi T) = _
  rw [Params.atD_phi_valid T hP]

theorem atD_a_eq_av (hP : P.Valid) (T : ℝ) :
    (P.atD T).a T = AdmWindow.av (P.phiD T) (P.L T) := by
  rw [Params.atD_a T hP]; rfl

theorem atD_tau_eq (P : Params) (T : ℝ) (k : ℤ) :
    (P.atD T).tau T k = T + k * (2 * π / P.L T) := rfl

/-! ### Eventual side conditions in T -/

lemma tendsto_L (hP : P.Valid) : Tendsto P.L atTop atTop := by
  have h : Tendsto (fun T : ℝ => Real.log (T / (2 * Real.pi))) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))
  exact (h.const_mul_atTop hP.lam_pos).congr fun T => by simp [Params.L, l]

lemma eventually_w8 (hP : P.Valid) : ∀ᶠ T in atTop, 8 * P.w ≤ P.L T :=
  (tendsto_L hP).eventually_ge_atTop _

lemma eventually_w4pi (hP : P.Valid) : ∀ᶠ T in atTop, 4 * π * P.w ≤ P.L T :=
  (tendsto_L hP).eventually_ge_atTop _

/-! ### 1/2 ≤ a_D ≤ 1 -/

theorem aD_range_of (hP : P.Valid) {T : ℝ} (h8 : 8 * P.w ≤ P.L T) (h4π : 4 * π * P.w ≤ P.L T) :
    1 / 2 ≤ (P.atD T).a T ∧ (P.atD T).a T ≤ 1 := by
  have hW := admWindow_params hP h8
  rw [atD_a_eq_av hP]
  refine ⟨?_, hW.av_le_one⟩
  calc (1 : ℝ) / 2 ≤ AdmWindow.bv (P.phiD T) (P.L T) :=
        bv_phiD_ge_half hP.taper hP.lam_pos hP.lam_le_one hP.one_le_w h8 h4π
    _ ≤ AdmWindow.av (P.phiD T) (P.L T) := hW.bv_le_av

theorem eventually_aD_range {P : Params} (hP : P.Valid) :
    ∀ᶠ T in atTop, 1 / 2 ≤ (P.atD T).a T ∧ (P.atD T).a T ≤ 1 := by
  filter_upwards [eventually_w8 hP, eventually_w4pi hP] with T h8 h4π
  exact aD_range_of hP h8 h4π

/-! ### lem:poisson for φ_D and prop:block -/

theorem poissonSqD (hP : P.Valid) {T : ℝ} (h8 : 8 * P.w ≤ P.L T) :
    ZeroSide.PoissonSq T (P.atD T) := by
  intro γ
  have hW := admWindow_params hP h8
  have h := hW.hasSum_vHatR_mul T γ γ
  rw [sub_self, hW.VPhiR_zero] at h
  simp only [atD_phiHatR hP, atD_a_eq_av hP, atD_tau_eq, Params.atD_L, sq]
  convert h using 1
  ring

theorem blockInputsD_of (Z : ZeroConfig) (hP : P.Valid) {T : ℝ} (h8 : 8 * P.w ≤ P.L T)
    (h4π : 4 * π * P.w ≤ P.L T) : Assembly.BlockInputs Z (P.atD T) T := by
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have ha := (aD_range_of hP h8 h4π).1
  exact ZeroSide.blockInputsAt Z (P.atD T) T (fun z => GzGp.phiHat_conj _ T z)
    (fun r => GzGp.phiHat_ofReal _ T r) (poissonSqD hP h8) hL
    (mul_pos (by linarith) (pow_pos hL 2))

theorem eventually_blockInputsD (Z : ZeroConfig) {P : Params} (hP : P.Valid) :
    ∀ᶠ T in atTop, Assembly.BlockInputs Z (P.atD T) T := by
  filter_upwards [eventually_w8 hP, eventually_w4pi hP] with T h8 h4π
  exact blockInputsD_of Z hP h8 h4π

/-! ### The H-EF bridge for φ_D -/

theorem GzGpD_of (Z : ZeroConfig) (H : PaperInputs Z) (hP : P.Valid) {T : ℝ}
    (h8 : 8 * P.w ≤ P.L T) : Z.Gz (P.atD T) T = (P.atD T).Gp T := by
  have hW := admWindow_params hP h8
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  refine Z.Gz_eq_Gp (P.atD T) T H.EF hL ?_ ?_
  · rw [Params.atD_phi_valid T hP]; exact hW.vC_contDiff
  · rw [Params.atD_phi_valid T hP]
    exact closure_minimal hW.support_subset isClosed_Icc

theorem eventually_GzGpD (Z : ZeroConfig) (H : PaperInputs Z) {P : Params} (hP : P.Valid) :
    ∀ᶠ T in atTop, Z.Gz (P.atD T) T = (P.atD T).Gp T := by
  filter_upwards [eventually_w8 hP] with T h8
  exact GzGpD_of Z H hP h8

/-! ### prop:tail for φ_D -/

/-- C₁(T) := ‖φ_D''‖₁ (the [eq:hfbound] constant for the window of height T). -/
def C1D (P : Params) (T : ℝ) : ℝ := ∫ u, |deriv (deriv (P.phiD T)) u|

lemma C1D_nonneg (P : Params) (T : ℝ) : 0 ≤ C1D P T :=
  integral_nonneg fun _ => abs_nonneg _

lemma C1D_le (hP : P.Valid) {T : ℝ} (h8 : 8 * P.w ≤ P.L T) : C1D P T ≤ cDT P.ϱ P.lam := by
  have hW := admWindow_params hP h8
  have h1 : C1D P T ≤ cDT P.ϱ P.lam / P.w := hW.l1_deriv2
  have hc : 0 ≤ cDT P.ϱ P.lam := hW.c_nonneg
  have hw := hP.one_le_w
  exact h1.trans (div_le_self hc hw)

/-- [eq:hfbound] for φ_D in the shape 'TailHyp.hdecay' asks. -/
theorem hdecayD (hP : P.Valid) {T : ℝ} (h8 : 8 * P.w ≤ P.L T) (r y : ℝ) (hy : |y| ≤ 1 / 2)
    (hz : (r : ℂ) - I * y ≠ 0) :
    ‖(P.atD T).phiHat T (r - I * y)‖
      ≤ Real.exp ((P.atD T).L T / 4) * C1D P T / ‖(r : ℂ) - I * y‖ ^ 2 := by
  have hW := admWindow_params hP h8
  have hL : 0 ≤ P.L T := hW.L_pos.le
  rw [atD_phiHat hP, Params.atD_L, le_div_iff₀ (by positivity)]
  refine le_trans (hW.norm_vHat_mul_sq_le _) ?_
  unfold C1D
  gcongr
  have him : ((r : ℂ) - I * y).im = -y := by simp
  rw [him, abs_neg]
  nlinarith

theorem eventually_tailPackageD (Z : ZeroConfig) (H : PaperInputs Z) {P : Params} (hP : P.Valid) :
    ∃ θ₀ : ℝ → ℝ, (∀ᶠ T in atTop, Assembly.TailInputs Z (P.atD T) T (θ₀ T)) ∧
      ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1) := by
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
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

end ThmD
end Zeta23

end
