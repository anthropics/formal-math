/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmD/Concrete.lean — the concrete FactsD instance.
Mirror of Zeta23/PrimeSideB/Traces.lean's concreteData/concreteFacts for the Montgomery–Taylor
window (paper §7.1): plugs BridgeD (P.localFunD, localHypsCoreD_eventually) and the
Core-flipped §5 results into the DataD/FactsD interface of Zeta23/ThmD/Traces.lean, with the
[thm:D]-specific fields discharged by ThmD/PP.lean (sumA2g_close) + ThmD/Window.lean
(gD_deriv_facts, jD_close et al.).  End product: TracesBoundsD for the concrete window, via
tracesBoundsD_of_factsD.
-/
import Zeta23.PrimeSideA
import Zeta23.PrimeSideB.Concrete
import Zeta23.PrimeSideB.Traces
import Zeta23.ThmD.Traces
import Zeta23.ThmD.BridgeD
import Zeta23.ThmD.PP

noncomputable section

open Real Filter Topology MeasureTheory
open scoped BigOperators ArithmeticFunction

namespace Zeta23
namespace ThmD

open PrimeSide PaperParams

variable (P : Params)

/-- the concrete D-data: the abstract prime-side expressions evaluated at the
Montgomery–Taylor window data P.localFunD T, plus the moment J_T of [eq:abJ]. -/
def concreteDataD (Z : ZeroConfig) : DataD P where
  aT := fun T => (P.localFunD T).a
  bT := fun T => (P.localFunD T).b
  trG := fun T => trGtA (P.toSetting T) (P.localFunD T)
  trG2 := fun T => trGt2A (P.toSetting T) (P.localFunD T)
  Ncnt := fun T => (Z.N T (2 * T) : ℝ)
  Mtot := fun T => MtotalA (P.toSetting T) (P.localFunD T)
  Mmumu := fun T => Mform (P.localFunD T).Phi T Zeta23.mu Zeta23.mu
  MPP := fun T => Mform (P.localFunD T).Phi T (Zeta23.PX (P.X T)) (Zeta23.PX (P.X T))
  MmuP := fun T => Mform (P.localFunD T).Phi T Zeta23.mu (Zeta23.PX (P.X T))
  MmuPi := fun T => Mform (P.localFunD T).Phi T Zeta23.mu (Zeta23.PiX (P.X T))
  MPPi := fun T => Mform (P.localFunD T).Phi T (Zeta23.PX (P.X T)) (Zeta23.PiX (P.X T))
  MPiPi := fun T => Mform (P.localFunD T).Phi T (Zeta23.PiX (P.X T)) (Zeta23.PiX (P.X T))
  intMu2 := fun T => ∫ τ in T..(2 * T), Zeta23.mu τ ^ 2
  sumL2g := fun T => sumA2g (P.X T) (P.localFunD T).g
  JT := fun T => 2 / P.L T ^ 3 * ∫ y in (0:ℝ)..(P.L T), (P.localFunD T).g y * y

variable {P}

/-- the CoreD analogue of LocalHypsEventually (= the conclusion of
BridgeD.localHypsCoreD_eventually). -/
def LocalHypsCoreDEventually (P : Params) : Prop :=
  ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    PrimeSide.LocalHypsCore (cDT P.ϱ P.lam) (P.toSetting T) (P.localFunD T)

/-- the CoreD analogue of PrimeSide.evBound_of_eventuallyAt. -/
lemma evBound_of_eventuallyAtCoreD (hLoc : LocalHypsCoreDEventually P)
    {f g : Setting → LocalFun → ℝ}
    (h : ∃ C : ℝ, EventuallyAtCore (cDT P.ϱ P.lam) P.lam (fun p F => |f p F| ≤ C * g p F))
    (hg : ∀ᶠ T in atTop, 0 ≤ g (P.toSetting T) (P.localFunD T)) :
    EvBound (fun T => f (P.toSetting T) (P.localFunD T))
      (fun T => g (P.toSetting T) (P.localFunD T)) := by
  obtain ⟨T₀, hT₀⟩ := hLoc
  obtain ⟨C, T₁, hT₁⟩ := h
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp hg
  refine ⟨max C 1, by positivity, max T₀ (max T₁ T₂), fun T hT => ?_⟩
  have h0 : T₀ ≤ T := (le_max_left _ _).trans hT
  have h1 : T₁ ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
  have h2 : T₂ ≤ T := ((le_max_right _ _).trans (le_max_right _ _)).trans hT
  have := hT₁ (P.toSetting T) (P.localFunD T) rfl h1 (hT₀ T h0)
  calc |f (P.toSetting T) (P.localFunD T)| ≤ C * g (P.toSetting T) (P.localFunD T) := this
    _ ≤ max C 1 * g (P.toSetting T) (P.localFunD T) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (hT₂ T h2)

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

/-- **FactsD for the concrete Montgomery–Taylor data.**  Inputs: P.Valid, PaperInputs Z
(H-RvM, H-Γ, H-cheb, H-MV), and the CoreD taper facts eventually (BridgeD). -/
theorem concreteFactsD {Z : ZeroConfig} (hP : P.Valid) (inp : PaperInputs Z)
    (hLoc : LocalHypsCoreDEventually P) : FactsD (concreteDataD P Z) := by
  have hlam : 0 < P.lam ∧ P.lam ≤ 1 := ⟨hP.lam_pos, hP.lam_le_one⟩
  have hΓ := inp.Gamma
  have hcheb := inp.cheb
  set cϱD := cDT P.ϱ P.lam with hcD
  have hreg : ∀ᶠ T in atTop, 0 ≤ T ∧ 0 ≤ l T ∧ 0 ≤ Real.log (l T) ∧ 0 ≤ P.L T ∧ 0 ≤ P.X T := by
    filter_upwards [eventually_ge_atTop 1, eventually_l_ge 1, eventually_log_l_ge 1,
      eventually_L_ge P hP.lam_pos 1, eventually_one_le_X P hP.lam_pos] with T h1 h2 h3 h4 h5
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨T₀, hT₀⟩ := id hLoc
  have e_ends := evBound_of_eventuallyAtCoreD hLoc
    (PrimeSide.lem_ends cϱD P.lam hΓ hcheb hlam) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact mul_nonneg (mul_nonneg (mul_nonneg hL hl) hlog) (add_nonneg (sq_nonneg _) hX))
  have e_mumu := evBound_of_eventuallyAtCoreD hLoc
    (PrimeSide.prop_mumu cϱD P.lam hΓ hcheb hlam) (by
    filter_upwards [hreg, eventually_L_ge P hP.lam_pos 1] with T ⟨hT, hl, hlog, hL, hX⟩ hL1
    exact mul_nonneg (sq_nonneg _) (Real.log_nonneg hL1))
  have e_PP := evBound_of_eventuallyAtCoreD hLoc
    (PrimeSide.prop_PP (cϱ := cϱD) (lam := P.lam) hcheb inp.MV hlam) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact mul_nonneg (sq_nonneg _) hX)
  have e_muP := evBound_of_eventuallyAtCoreD hLoc
    (PrimeSide.prop_cross_muP cϱD P.lam hΓ hcheb hlam) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact mul_nonneg hl (Real.sqrt_nonneg _))
  have e_muPi := evBound_of_eventuallyAtCoreD hLoc
    (PrimeSide.prop_cross_muPi cϱD P.lam hΓ hcheb hlam) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact mul_nonneg (mul_nonneg hl hL) (Real.sqrt_nonneg _))
  have e_PPi := evBound_of_eventuallyAtCoreD hLoc
    (PrimeSide.prop_cross_PPi cϱD P.lam hΓ hcheb hlam) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact mul_nonneg hL hX)
  have e_PiPi := evBound_of_eventuallyAtCoreD hLoc
    (PrimeSide.prop_cross_PiPi cϱD P.lam hΓ hcheb hlam) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact div_nonneg (mul_nonneg hL hX) hT)
  refine ⟨hP.lam_pos, hP.lam_le_one, hP.one_le_w, ?ab_range, rvm_evBound inp.RvM, ?muints2,
    ?prop_trace, e_ends, ?Msplit, e_mumu, e_PP, ?sumJ, e_muP, e_muPi, e_PPi, e_PiPi⟩
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
    obtain ⟨C, T₁, hC⟩ := hΓ.int_mu_sq
    refine ⟨max C 1, by positivity, max T₁ 0, fun T hT =>
      (hC T ((le_max_left _ _).trans hT)).trans ?_⟩
    have hT0 : 0 ≤ T := (le_max_right _ _).trans hT
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_right (le_max_left _ _) ?_
    exact div_nonneg (div_nonneg (mul_nonneg hT0 (sq_nonneg _)) (by positivity)) (sq_nonneg _)
  case prop_trace =>
    obtain ⟨A, hA, T₁, hN⟩ := rvm_evBound inp.RvM
    obtain ⟨C, T₂, hC⟩ := PrimeSide.prop_trace cϱD P.lam hΓ hcheb hlam A
    refine ⟨max C 1, by positivity, max T₀ (max T₁ T₂), fun T hT => ?_⟩
    have h0 : T₀ ≤ T := (le_max_left _ _).trans hT
    have h1 : T₁ ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
    have h2 : T₂ ≤ T := ((le_max_right _ _).trans (le_max_right _ _)).trans hT
    have hF := hT₀ T h0
    have := hC (P.toSetting T) (P.localFunD T) rfl h2 hF (Z.N T (2 * T) : ℝ) (hN T h1)
    refine this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    exact mul_nonneg hF.L_pos.le (Real.sqrt_nonneg _)
  case Msplit =>
    filter_upwards [eventually_ge_atTop T₀] with T hT
    exact eq_Msplit cϱD hΓ (P.toSetting T) (P.localFunD T) (hT₀ T hT)
  case sumJ =>
    obtain ⟨C, hC0, hC⟩ := ThmD.sumA2g_close hcheb
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
    have e : P.L T ^ 3 / 2 * ((concreteDataD P Z).JT T)
        = ∫ y in (0:ℝ)..(P.L T), (P.localFunD T).g y * y := by
      show P.L T ^ 3 / 2 * (2 / P.L T ^ 3 * ∫ y in (0:ℝ)..(P.L T), (P.localFunD T).g y * y) = _
      field_simp
    show |sumA2g (P.X T) (P.localFunD T).g - P.L T ^ 3 / 2 * ((concreteDataD P Z).JT T)|
      ≤ C * P.L T ^ 2
    rw [e]
    exact key

/-- **TracesBoundsD for the concrete Montgomery–Taylor window.** -/
theorem tracesBoundsD_concrete {Z : ZeroConfig} (hP : P.Valid) (inp : PaperInputs Z)
    (hLoc : LocalHypsCoreDEventually P) :
    TracesBoundsD P (concreteDataD P Z).aT (concreteDataD P Z).bT (concreteDataD P Z).JT
      (concreteDataD P Z).trG (concreteDataD P Z).trG2 (concreteDataD P Z).Ncnt :=
  tracesBoundsD_of_factsD _ (concreteFactsD hP inp hLoc)

end ThmD
end Zeta23
