/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmDE/Concrete.lean — the concrete FactsDChi instance:
Zeta23/ThmE/TracesChi.lean's concreteFactsChi (the χ prime side from PaperInputsChi) re-run for the
Montgomery–Taylor window data P.localFunD T (BridgeD: LocalHypsCore eventually), with the
[eq:gbounds] sandwich replaced by the coprime partial-summation step (Zeta23/ThmDE/PP.lean) and the
window moments (a_D, b_D, J_D) kept symbolic — exactly as Zeta23/ThmD/Concrete.lean does for ζ.
End product: TracesBoundsDChi for the concrete window (tracesBoundsDChi_concrete), plus the
identification of the Params-level χ-traces of the window-realizing family P.atD with these data.
-/
import Zeta23.ThmDE.Traces
import Zeta23.ThmDE.PP
import Zeta23.ThmD.Concrete
import Zeta23.ThmD.ParamsD

noncomputable section

open Real Filter Topology MeasureTheory
open scoped BigOperators ArithmeticFunction

namespace Zeta23

namespace Params

/-- the Params-level χ prime-side traces of 'P.atD T' at height T are the abstract-layer χ-traces
of the D-data (rfl bridges + atD_localFun). -/
theorem atD_trGtildeChi {P : Params} (hP : P.Valid) (κ q : ℕ) (c : ℕ → ℂ) (T : ℝ) :
    ThmE.trGtildeChi (P.atD T) κ q c T = ThmE.trGtChiA κ q c (P.toSetting T) (P.localFunD T) := by
  rw [← ThmE.trGtChiA_concrete (P.atD T) κ q c T, atD_localFun T hP]; rfl

theorem atD_trGtildeSqChi {P : Params} (hP : P.Valid) (κ q : ℕ) (c : ℕ → ℂ) (T : ℝ) :
    ThmE.trGtildeSqChi (P.atD T) κ q c T
      = ThmE.trGt2ChiA κ q c (P.toSetting T) (P.localFunD T) := by
  rw [← ThmE.trGt2ChiA_concrete (P.atD T) κ q c T, atD_localFun T hP]; rfl

end Params

namespace ThmDE

open ThmD ThmE PrimeSide PaperParams

variable (P : Params) (κ q : ℕ) (c : ℕ → ℂ)

/-- the concrete χ-D data: the abstract χ prime-side expressions at the Montgomery–Taylor window
data P.localFunD T, plus J_T [eq:abJ] and the coprime sum. -/
def concreteDataDChi (Z : ZeroConfig) : DataDChi P where
  aT := fun T => (P.localFunD T).a
  bT := fun T => (P.localFunD T).b
  trG := fun T => trGtChiA κ q c (P.toSetting T) (P.localFunD T)
  trG2 := fun T => trGt2ChiA κ q c (P.toSetting T) (P.localFunD T)
  Ncnt := fun T => (Z.N T (2 * T) : ℝ)
  Mtot := fun T => MtotalChiA κ q c (P.toSetting T) (P.localFunD T)
  Mmumu := fun T => Mform (P.localFunD T).Phi T (muq κ q) (muq κ q)
  MPP := fun T => Mform (P.localFunD T).Phi T (PXc c (P.X T)) (PXc c (P.X T))
  MmuP := fun T => Mform (P.localFunD T).Phi T (muq κ q) (PXc c (P.X T))
  intMu2 := fun T => ∫ τ in T..(2 * T), muq κ q τ ^ 2
  sumL2gq := fun T => sumA2gCoprime q (P.X T) (P.localFunD T).g
  JT := fun T => 2 / P.L T ^ 3 * ∫ y in (0:ℝ)..(P.L T), (P.localFunD T).g y * y

variable {P κ q c}

/-- vanishing of the autocorrelation beyond the support width. -/
private lemma autocorr_eq_zero_of_support {h : ℝ → ℝ} {M : ℝ}
    (hsupp : ∀ u : ℝ, M ≤ |u| → h u = 0) {y : ℝ} (hy : 2 * M ≤ |y|) (_hM : 0 ≤ M) :
    Params.autocorr h y = 0 := by
  show ∫ u, h u * h (u + y) = 0
  have hz : ∀ u : ℝ, h u * h (u + y) = 0 := by
    intro u
    rcases le_or_gt M (|u|) with hu | hu
    · rw [hsupp u hu, zero_mul]
    · have : M ≤ |u + y| := by
        have h1 := abs_sub_abs_le_abs_sub y (-u)
        rw [abs_neg, sub_neg_eq_add] at h1
        have h2 : |y + u| = |u + y| := by rw [add_comm]
        rw [h2] at h1
        linarith
      rw [hsupp _ this, mul_zero]
  simp only [hz, MeasureTheory.integral_zero]

set_option maxHeartbeats 1600000 in
/-- **FactsDChi for the concrete Montgomery–Taylor data of L(s,χ).** Inputs: P.Valid, 1 ≤ q,
unimodular coefficients, PaperInputsChi (H-RvM(χ), H-Γ(χ), H-cheb, H-cheb-coprime, H-MV), and the
CoreD taper facts eventually (BridgeD). -/
theorem concreteFactsDChi {Z : ZeroConfig} (hP : P.Valid) (hq : 1 ≤ q)
    (hcu : CoeffUnimodular q c) (inp : PaperInputsChi κ q c Z)
    (hLoc : ThmD.LocalHypsCoreDEventually P) : FactsDChi q (concreteDataDChi P κ q c Z) := by
  have hlam : 0 < P.lam ∧ P.lam ≤ 1 := ⟨hP.lam_pos, hP.lam_le_one⟩
  have hΓq := inp.Gamma
  have hcheb := inp.cheb
  have hc : CoeffOK q c := hcu.toCoeffOK
  set cϱD := cDT P.ϱ P.lam with hcD
  have hreg : ∀ᶠ T in atTop, 0 ≤ T ∧ 0 ≤ l T ∧ 0 ≤ Real.log (l T) ∧ 0 ≤ P.L T ∧ 0 ≤ P.X T := by
    filter_upwards [eventually_ge_atTop 1, eventually_l_ge 1, eventually_log_l_ge 1,
      eventually_L_ge P hP.lam_pos 1, eventually_one_le_X P hP.lam_pos] with T h1 h2 h3 h4 h5
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨T₀, hT₀⟩ := id hLoc
  have e_ends := ThmD.evBound_of_eventuallyAtCoreD hLoc
    (lem_ends_chi (κ := κ) (q := q) (c := c) (cϱ := cϱD) (lam := P.lam) hΓq hcheb hc hlam hq) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact mul_nonneg (mul_nonneg (mul_nonneg hL hl) hlog) (add_nonneg (sq_nonneg _) hX))
  have e_mumu := ThmD.evBound_of_eventuallyAtCoreD hLoc
    (prop_mumu_chi (cϱ := cϱD) (lam := P.lam) hΓq hc hq hlam) (by
    filter_upwards [hreg, eventually_L_ge P hP.lam_pos 1] with T ⟨hT, hl, hlog, hL, hX⟩ hL1
    exact mul_nonneg (sq_nonneg _) (Real.log_nonneg hL1))
  have e_PP := ThmD.evBound_of_eventuallyAtCoreD hLoc
    (prop_PP_chi (cϱ := cϱD) (lam := P.lam) hcheb inp.MV hcu hlam) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact mul_nonneg (sq_nonneg _) hX)
  have e_muP := ThmD.evBound_of_eventuallyAtCoreD hLoc
    (prop_cross_muP_chi_proved (cϱ := cϱD) (lam := P.lam) hΓq hcheb hc hq hlam) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact mul_nonneg hl (Real.sqrt_nonneg _))
  refine ⟨hP.lam_pos, hP.lam_le_one, hP.one_le_w, hq, ?ab_range, rvm_evBound_chi inp.RvM,
    ?muints2, ?prop_trace, e_ends, ?Msplit, e_mumu, e_PP, ?sumJ, e_muP⟩
  case ab_range =>
    filter_upwards [eventually_ge_atTop T₀, eventually_L_ge P hP.lam_pos 8,
      eventually_L_ge P hP.lam_pos (2 * P.w)] with T hT hL8 hLw
    have hF := hT₀ T hT
    have hL0 : 0 < P.L T := by linarith
    refine ⟨hF.b_ge_half, hF.b_le_a, hF.a_le_one, ?_, ?_⟩
    · apply mul_nonneg (by positivity)
      apply intervalIntegral.integral_nonneg (by linarith : (0:ℝ) ≤ P.L T)
      intro y hy
      exact mul_nonneg (hF.g_nonneg y) hy.1
    · have hgcont : Continuous (P.localFunD T).g := by
        have hw0 : 0 < P.w := by linarith [hP.one_le_w]
        have hg := gD_deriv_facts hP.taper hP.lam_pos hP.lam_le_one hw0 hLw
        exact hg.1.continuous
      have hgle : ∀ y ∈ Set.Icc (0:ℝ) (P.L T), (P.localFunD T).g y * y ≤ P.L T * y := by
        intro y hy
        apply mul_le_mul_of_nonneg_right _ hy.1
        calc (P.localFunD T).g y ≤ (P.localFunD T).Aphi y := hF.g_le_Aphi y
          _ ≤ max ((P.toSetting T).L - |y|) 0 := hF.Aphi_le y
          _ ≤ P.L T := by
              apply max_le _ hL0.le
              have := abs_nonneg y
              show (P.toSetting T).L - |y| ≤ P.L T
              have e : (P.toSetting T).L = P.L T := rfl
              rw [e]
              linarith
      have hIle : ∫ y in (0:ℝ)..(P.L T), (P.localFunD T).g y * y
          ≤ ∫ y in (0:ℝ)..(P.L T), P.L T * y := by
        apply intervalIntegral.integral_mono_on (by linarith : (0:ℝ) ≤ P.L T) ?_ ?_ hgle
        · exact (hgcont.mul continuous_id).intervalIntegrable 0 (P.L T)
        · exact (continuous_const.mul continuous_id).intervalIntegrable 0 (P.L T)
      have hIval : ∫ y in (0:ℝ)..(P.L T), P.L T * y = P.L T ^ 3 / 2 := by
        rw [intervalIntegral.integral_const_mul, integral_id]
        ring
      calc 2 / P.L T ^ 3 * ∫ y in (0:ℝ)..(P.L T), (P.localFunD T).g y * y
          ≤ 2 / P.L T ^ 3 * (P.L T ^ 3 / 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [← hIval]
            exact hIle
        _ = 1 := by field_simp
  case muints2 =>
    obtain ⟨C, T₁, hC⟩ := hΓq.int_mu_sq
    refine ⟨max C 1, by positivity, max T₁ 0, fun T hT =>
      (hC T ((le_max_left _ _).trans hT)).trans ?_⟩
    have hT0 : 0 ≤ T := (le_max_right _ _).trans hT
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_right (le_max_left _ _) ?_
    exact div_nonneg (div_nonneg (mul_nonneg hT0 (sq_nonneg _)) (by positivity)) (sq_nonneg _)
  case prop_trace =>
    obtain ⟨A, hA, T₁, hN⟩ := rvm_evBound_chi inp.RvM
    obtain ⟨C, T₂, hC⟩ := prop_trace_chi (κ := κ) (q := q) (c := c) (cϱ := cϱD)
      (lam := P.lam) hΓq hcheb hc hlam A hq
    refine ⟨max C 1, by positivity, max (max T₀ 1) (max T₁ T₂), fun T hT => ?_⟩
    have h0 : T₀ ≤ T := ((le_max_left _ _).trans (le_max_left _ _)).trans hT
    have hT1' : (1:ℝ) ≤ T := ((le_max_right _ _).trans (le_max_left _ _)).trans hT
    have h1 : T₁ ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
    have h2 : T₂ ≤ T := ((le_max_right _ _).trans (le_max_right _ _)).trans hT
    have hF := hT₀ T h0
    have hT0' : (0:ℝ) < T := by linarith
    have hNT : |(Z.N T (2 * T) : ℝ) - T / (2 * π) * ell1q q T| ≤ A * Real.log T := by
      have hl : l T ≤ Real.log T := by
        unfold Zeta23.l
        rw [Real.log_div hT0'.ne' (by positivity)]
        have : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
        linarith
      have hN' := hN T h1
      simp only at hN'
      rw [show T * ell1q q T / (2 * π) = T / (2 * π) * ell1q q T by ring] at hN'
      calc |(Z.N T (2 * T) : ℝ) - T / (2 * π) * ell1q q T| ≤ A * l T := hN'
        _ ≤ A * Real.log T := mul_le_mul_of_nonneg_left hl hA.le
    have key := hC (P.toSetting T) (P.localFunD T) rfl h2 hF (Z.N T (2 * T) : ℝ) hNT
    refine key.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    exact mul_nonneg hF.L_pos.le (Real.sqrt_nonneg _)
  case Msplit =>
    obtain ⟨T₁, hT₁⟩ := eq_Msplit_chi (κ := κ) (q := q) (c := c) (cϱ := cϱD) (lam := P.lam)
      hΓq hc hlam
    filter_upwards [eventually_ge_atTop T₀, eventually_ge_atTop T₁] with T h0 h1
    exact hT₁ (P.toSetting T) (P.localFunD T) rfl h1 (hT₀ T h0)
  case sumJ =>
    obtain ⟨C, hC0, hC⟩ := ThmDE.sumA2gCoprime_close inp.chebq
    refine ⟨C, hC0, ?_⟩
    obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp (eventually_L_ge P hP.lam_pos 8)
    obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp (eventually_L_ge P hP.lam_pos (2 * P.w))
    refine ⟨max T₀ (max T₁ T₂), fun T hT => ?_⟩
    have h1 : T₁ ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
    have h2 : T₂ ≤ T := ((le_max_right _ _).trans (le_max_right _ _)).trans hT
    have hL8 : 8 ≤ P.L T := hT₁ T h1
    have hLw : 2 * P.w ≤ P.L T := hT₂ T h2
    have hw0 : 0 < P.w := by linarith [hP.one_le_w]
    have hL0 : 0 < P.L T := by linarith
    have hg := gD_deriv_facts hP.taper hP.lam_pos hP.lam_le_one hw0 hLw
    have hgsupp : ∀ y : ℝ, P.L T ≤ y → (P.localFunD T).g y = 0 := by
      intro y hy
      show Params.autocorr (fun u => phiD P.ϱ P.lam (P.L T) P.w u ^ 2) y = 0
      apply autocorr_eq_zero_of_support (M := P.L T / 2) ?_ ?_ (by linarith)
      · intro u hu
        rw [phiD_eq_zero hP.taper hw0 hu, zero_pow two_ne_zero]
      · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ y)]
        linarith
    have key := hC (P.L T) (P.X T) (P.localFunD T).g hL8 (by
        show P.X T = Real.exp (P.L T)
        rfl) hg.1 hg.2.1 hg.2.2 hgsupp
    have e : P.L T ^ 3 / 2 * ((concreteDataDChi P κ q c Z).JT T)
        = ∫ y in (0:ℝ)..(P.L T), (P.localFunD T).g y * y := by
      show P.L T ^ 3 / 2 * (2 / P.L T ^ 3 * ∫ y in (0:ℝ)..(P.L T), (P.localFunD T).g y * y) = _
      field_simp
    show |sumA2gCoprime q (P.X T) (P.localFunD T).g - P.L T ^ 3 / 2 * ((concreteDataDChi P κ q c Z).JT T)|
      ≤ C * P.L T ^ 2
    rw [e]
    exact key

/-- **TracesBoundsDChi for the concrete Montgomery–Taylor window and L(s,χ).** -/
theorem tracesBoundsDChi_concrete {Z : ZeroConfig} (hP : P.Valid) (hq : 1 ≤ q)
    (hcu : CoeffUnimodular q c) (inp : PaperInputsChi κ q c Z)
    (hLoc : ThmD.LocalHypsCoreDEventually P) :
    TracesBoundsDChi P q (concreteDataDChi P κ q c Z).aT (concreteDataDChi P κ q c Z).bT
      (concreteDataDChi P κ q c Z).JT (concreteDataDChi P κ q c Z).trG
      (concreteDataDChi P κ q c Z).trG2 (concreteDataDChi P κ q c Z).Ncnt :=
  tracesBoundsDChi_of_factsDChi _ (concreteFactsDChi hP hq hcu inp hLoc)

end ThmDE
end Zeta23

end
