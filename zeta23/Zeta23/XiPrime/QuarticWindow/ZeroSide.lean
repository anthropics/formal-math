/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/QuarticWindow/ZeroSide.lean — the zero side for a MODULATED window P.atV v, and the quartic instance.

§1 is GENERIC in the profile v: given an admissibility witness T ↦ AdmWindow (P.phiV v T) (P.L T) P.w cW and the lower
bound 1/2 ≤ a_V(T) (both for 8w ≤ L_T), it proves lem:poisson, prop:block, the H-EF bridge, prop:tail (from the local zero
count only) and the bundle
  windowZeroSide_atV_of : RiemannVonMangoldt Z → P.Valid → XiPrime.WindowZeroSide Z P (P.atV v)
(the general-profile family and the flat window can instantiate it as well).
§2 is the quartic instance: 1/2 ≤ a_Q ≤ 1 at 8w ≤ L (a_Q ≥ (27/40)(1 − 2w/L) ≥ 81/160) and windowZeroSide_atV.
-/
import Zeta23.XiPrime.QuarticWindow.Quartic
import Zeta23.XiPrime.Assembly
import Zeta23.ZeroSide
import Zeta23.Tail
import Zeta23.Hypotheses.GzGp

noncomputable section

open Filter Complex Real Set MeasureTheory

namespace Zeta23
namespace XiPrime

variable {P : Params}

theorem atV_tau_eq (P : Params) (v : ℝ → ℝ) (T : ℝ) (k : ℤ) :
    (P.atV v T).tau T k = T + k * (2 * π / P.L T) := rfl

/-! ## §1. Generic profile -/

section generic

variable {v : ℝ → ℝ} {cW : ℝ} (hP : P.Valid) (hv : ∀ s, v (-s) = v s)
  (hW : ∀ T : ℝ, 8 * P.w ≤ P.L T → AdmWindow (P.phiV v T) (P.L T) P.w cW)
  (ha : ∀ᶠ T in atTop, 1 / 2 ≤ (P.atV v T).a T)
include hP hv hW

/-! ### lem:poisson and prop:block -/

theorem poissonSqV_of {T : ℝ} (h8 : 8 * P.w ≤ P.L T) : ZeroSide.PoissonSq T (P.atV v T) := by
  intro γ
  have h := (hW T h8).hasSum_vHatR_mul T γ γ
  rw [sub_self, (hW T h8).VPhiR_zero] at h
  simp only [Params.atV_phiHatR T hP hv, Params.atV_a T hP hv, atV_tau_eq, Params.atV_L, sq]
  convert h using 1
  ring

theorem blockInputsV_of' (Z : ZeroConfig) {T : ℝ} (h8 : 8 * P.w ≤ P.L T) (haT : 0 < (P.atV v T).a T) :
    Assembly.BlockInputs Z (P.atV v T) T := by
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  exact ZeroSide.blockInputsAt Z (P.atV v T) T (fun z => GzGp.phiHat_conj _ T z)
    (fun r => GzGp.phiHat_ofReal _ T r) (poissonSqV_of hP hv hW h8) hL (mul_pos haT (pow_pos hL 2))

/-! ### the H-EF bridge -/

theorem GzGpV_of' (Z : ZeroConfig) (hEF : ExplicitFormulaPaper Z) {T : ℝ} (h8 : 8 * P.w ≤ P.L T) :
    Z.Gz (P.atV v T) T = (P.atV v T).Gp T := by
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  refine Z.Gz_eq_Gp (P.atV v T) T hEF hL ?_ ?_
  · rw [Params.atV_phi_valid T hP hv]; exact (hW T h8).vC_contDiff
  · rw [Params.atV_phi_valid T hP hv]; exact closure_minimal (hW T h8).support_subset isClosed_Icc

/-! ### prop:tail -/

omit hP hv hW in
/-- C₁(T) := ‖φ_V″‖₁. -/
lemma C1Vv_nonneg (P : Params) (v : ℝ → ℝ) (T : ℝ) : 0 ≤ ∫ u, |deriv (deriv (P.phiV v T)) u| :=
  integral_nonneg fun _ => abs_nonneg _

omit hv in
lemma C1Vv_le {T : ℝ} (h8 : 8 * P.w ≤ P.L T) : ∫ u, |deriv (deriv (P.phiV v T)) u| ≤ cW :=
  (hW T h8).l1_deriv2.trans (div_le_self (hW T h8).c_nonneg hP.one_le_w)

theorem hdecayV_of {T : ℝ} (h8 : 8 * P.w ≤ P.L T) (r y : ℝ) (hy : |y| ≤ 1 / 2) (hz : (r : ℂ) - I * y ≠ 0) :
    ‖(P.atV v T).phiHat T (r - I * y)‖
      ≤ Real.exp ((P.atV v T).L T / 4) * (∫ u, |deriv (deriv (P.phiV v T)) u|) / ‖(r : ℂ) - I * y‖ ^ 2 := by
  have hL : 0 ≤ P.L T := (hW T h8).L_pos.le
  rw [Params.atV_phiHat T hP hv, Params.atV_L, le_div_iff₀ (by positivity)]
  refine le_trans ((hW T h8).norm_vHat_mul_sq_le _) ?_
  gcongr
  have him : ((r : ℂ) - I * y).im = -y := by simp
  rw [him, abs_neg]
  nlinarith

include ha in
theorem eventually_tailPackageV_of (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) :
    ∃ θ₀ : ℝ → ℝ, (∀ᶠ T in atTop, Assembly.TailInputs Z (P.atV v T) T (θ₀ T)) ∧
      ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1) := by
  refine ⟨fun T => Tail.theta0 A₀ (Real.exp (P.L T / 4) * ∫ u, |deriv (deriv (P.phiV v T)) u|) T, ?_, ?_⟩
  · have hL2 : ∀ᶠ T in atTop, 2 ≤ P.L T := (Params.tendsto_L_of_valid hP).eventually_ge_atTop 2
    filter_upwards [eventually_ge_atTop Tail.T₀, hL2, Params.eventually_w8 hP, ha] with T hT hL h8 haT
    have HT : Tail.TailHyp Z (P.atV v T) T A₀ (∫ u, |deriv (deriv (P.phiV v T)) u|) :=
      { hT := hT, hL := hL, hA₀ := hA₀, hloc := hloc, hC₁ := C1Vv_nonneg P v T,
        hdecay := fun r y hy hz => hdecayV_of hP hv hW h8 r y hy hz }
    have ha' : 0 < (P.atV v T).a T := by linarith
    exact HT.tailInputs ha' (fun z => GzGp.phiHat_conj _ T z)
  · exact Tail.eventually_theta0_le P hP hA₀ (fun T => ∫ u, |deriv (deriv (P.phiV v T)) u|)
      (C1Vv_nonneg P v) (R := cW / 2) ((Params.eventually_w8 hP).mono fun T h8 => by linarith [C1Vv_le hP hW h8])

/-! ### The generic bundle -/

include ha in
/-- **the zero side of a modulated window**, from an admissibility witness and a_V ≥ 1/2. -/
theorem windowZeroSide_atV_of (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) : WindowZeroSide Z P (P.atV v) := by
  obtain ⟨A₀, hA₀, hloc⟩ := hR.local_count
  refine ⟨fun _ => rfl, fun _ => rfl, ?_, eventually_tailPackageV_of hP hv hW ha Z hA₀ hloc, ?_⟩
  · filter_upwards [Params.eventually_w8 hP] with T h8
    exact poissonSqV_of hP hv hW h8
  · exact ha

end generic

/-! ## §2. The quartic instance -/

theorem atVQ_a_eq_av (hP : P.Valid) (T : ℝ) :
    (P.atV vQuartic T).a T = AdmWindow.av (P.phiV vQuartic T) (P.L T) :=
  Params.atV_a T hP vQuartic_even

theorem atVQ_phiHat (hP : P.Valid) (T : ℝ) :
    (P.atV vQuartic T).phiHat T = AdmWindow.vHat (P.phiV vQuartic T) :=
  Params.atV_phiHat T hP vQuartic_even

theorem atVQ_phiHatR (hP : P.Valid) (T : ℝ) :
    (P.atV vQuartic T).phiHatR T = AdmWindow.vHatR (P.phiV vQuartic T) :=
  Params.atV_phiHatR T hP vQuartic_even

/-! ### 1/2 ≤ a_V ≤ 1 -/

/-- φ_Q² ≥ (27/40)·φ² pointwise (on the core v ≥ 27/40; off it both vanish). -/
lemma phiV_quartic_sq_ge (hP : P.Valid) {T : ℝ} (h8 : 8 * P.w ≤ P.L T) (u : ℝ) :
    27 / 40 * P.phi T u ^ 2 ≤ P.phiV vQuartic T u ^ 2 := by
  have hw0 : 0 < P.w := by linarith [hP.one_le_w]
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  rw [Params.phiV_eq, mul_pow, ← Params.phi_eq]
  rcases le_or_gt (P.L T / 2) |u| with hu | hu
  · rw [Params.phi_eq_zero hP hu]; simp
  · have hmem := core_mem hL hu.le
    have hv := vQuartic_ge hmem
    rw [Real.sq_sqrt (le_max_left _ _), max_eq_right (by linarith)]
    exact mul_le_mul_of_nonneg_right hv (sq_nonneg _)

set_option maxHeartbeats 1600000 in
theorem aV_range_of (hP : P.Valid) {T : ℝ} (h8 : 8 * P.w ≤ P.L T) :
    1 / 2 ≤ (P.atV vQuartic T).a T ∧ (P.atV vQuartic T).a T ≤ 1 := by
  have hW := admWindow_phiV_quartic hP h8
  rw [atVQ_a_eq_av hP]
  refine ⟨?_, hW.av_le_one⟩
  have hw0 : 0 < P.w := by linarith [hP.one_le_w]
  have h2 : 2 * P.w ≤ P.L T := by linarith
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  -- av ≥ (27/40)·aConst ≥ (27/40)(1 − 2w/L) ≥ (27/40)(3/4)
  have hb : 1 - 2 * P.w / P.L T ≤ P.a T :=
    (Taper.one_sub_le_bConst hP.taper hw0 h2).trans (Taper.bConst_le_aConst hP.taper hw0 h2)
  have hwL : 2 * P.w / P.L T ≤ 1 / 4 := by rw [div_le_iff₀ hL]; linarith
  have hint : Integrable (fun u => P.phiV vQuartic T u ^ 2) := hW.integrable_pow two_pos
  have hint' : Integrable (fun u => 27 / 40 * P.phi T u ^ 2) :=
    ((Params.phi_continuous hP (by linarith)).fun_pow 2 |>.integrable_of_hasCompactSupport
      ((Params.phi_hasCompactSupport hP).comp_left (g := fun t => t ^ 2) (by norm_num))).const_mul _
  have hcmp : 27 / 40 * ∫ u, P.phi T u ^ 2 ≤ ∫ u, P.phiV vQuartic T u ^ 2 := by
    rw [← integral_const_mul]
    exact integral_mono hint' hint (phiV_quartic_sq_ge hP h8)
  have ha : P.a T = (P.L T)⁻¹ * ∫ u, P.phi T u ^ 2 := rfl
  unfold AdmWindow.av
  rw [ha] at hb
  have hLi : 0 < (P.L T)⁻¹ := inv_pos.mpr hL
  calc (1:ℝ) / 2 ≤ 27 / 40 * (1 - 2 * P.w / P.L T) := by nlinarith
    _ ≤ 27 / 40 * ((P.L T)⁻¹ * ∫ u, P.phi T u ^ 2) := by gcongr
    _ = (P.L T)⁻¹ * (27 / 40 * ∫ u, P.phi T u ^ 2) := by ring
    _ ≤ (P.L T)⁻¹ * ∫ u, P.phiV vQuartic T u ^ 2 := mul_le_mul_of_nonneg_left hcmp hLi.le

theorem eventually_aV_range (hP : P.Valid) :
    ∀ᶠ T in atTop, 1 / 2 ≤ (P.atV vQuartic T).a T ∧ (P.atV vQuartic T).a T ≤ 1 := by
  filter_upwards [Params.eventually_w8 hP] with T h8
  exact aV_range_of hP h8

/-! ### the quartic exports (instances of §1) -/

theorem poissonSqV (hP : P.Valid) {T : ℝ} (h8 : 8 * P.w ≤ P.L T) : ZeroSide.PoissonSq T (P.atV vQuartic T) :=
  poissonSqV_of hP vQuartic_even (fun _ h => admWindow_phiV_quartic hP h) h8

theorem blockInputsV_of (Z : ZeroConfig) (hP : P.Valid) {T : ℝ} (h8 : 8 * P.w ≤ P.L T) :
    Assembly.BlockInputs Z (P.atV vQuartic T) T :=
  blockInputsV_of' hP vQuartic_even (fun _ h => admWindow_phiV_quartic hP h) Z h8 (by linarith [(aV_range_of hP h8).1])

theorem eventually_blockInputsV (Z : ZeroConfig) (hP : P.Valid) :
    ∀ᶠ T in atTop, Assembly.BlockInputs Z (P.atV vQuartic T) T := by
  filter_upwards [Params.eventually_w8 hP] with T h8
  exact blockInputsV_of Z hP h8

theorem GzGpV_of (Z : ZeroConfig) (hEF : ExplicitFormulaPaper Z) (hP : P.Valid) {T : ℝ}
    (h8 : 8 * P.w ≤ P.L T) : Z.Gz (P.atV vQuartic T) T = (P.atV vQuartic T).Gp T :=
  GzGpV_of' hP vQuartic_even (fun _ h => admWindow_phiV_quartic hP h) Z hEF h8

theorem eventually_GzGpV (Z : ZeroConfig) (hEF : ExplicitFormulaPaper Z) (hP : P.Valid) :
    ∀ᶠ T in atTop, Z.Gz (P.atV vQuartic T) T = (P.atV vQuartic T).Gp T := by
  filter_upwards [Params.eventually_w8 hP] with T h8
  exact GzGpV_of Z hEF hP h8

theorem eventually_tailPackageV (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) (hP : P.Valid) :
    ∃ θ₀ : ℝ → ℝ, (∀ᶠ T in atTop, Assembly.TailInputs Z (P.atV vQuartic T) T (θ₀ T)) ∧
      ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1) :=
  eventually_tailPackageV_of hP vQuartic_even (fun _ h => admWindow_phiV_quartic hP h)
    ((eventually_aV_range hP).mono fun _ h => h.1) Z hA₀ hloc

/-- **The quartic window's zero side.** -/
theorem windowZeroSide_atV (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) (hP : P.Valid) :
    WindowZeroSide Z P (P.atV vQuartic) :=
  windowZeroSide_atV_of hP vQuartic_even (fun _ h => admWindow_phiV_quartic hP h)
    ((eventually_aV_range hP).mono fun _ h => h.1) Z hR

end XiPrime
end Zeta23

end
