/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
  Part of the Zeta23 formalization of the paper
  "More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/
import Zeta23.PrimeSideB
import Zeta23.PrimeSideB.Concrete
import Zeta23.PrimeSideA
import Zeta23.PrimeSideB.PP
import Zeta23.Hypotheses

/-!
# [thm:traces] for the concrete data — instantiating the abstract assembly
`Zeta23/PrimeSideB.lean` proves [thm:traces] for abstract real functions of `T`
(`PrimeSide.Facts D → TracesBounds …`).  This file plugs in the concrete objects:

* `Params.toSetting P T = ⟨T, λ, w⟩` and `Params.localFun P T = ⟨φ̂, Φ, A_φ, g, a, b⟩(T)` turn
  (`P : Params`, `T`) into the abstract prime-side layer (`Setting`, `LocalFun`), and
  `trGtA (P.toSetting T) (P.localFun T) = P.trGtilde T` etc. hold by `rfl`;
* `PrimeSide.concreteData P Z` is the `Data P` record of the actual traces / 𝓜-terms / ∫μ² / Σa_n²g;
* `PrimeSide.concreteFacts` derives `Facts (concreteData P Z)` from `P.Valid`, `PaperInputs Z`
  (H-RvM, H-Γ, H-cheb, H-MV), [prop:trace]/[lem:ends]/[eq:Msplit]/[prop:mumu]/[prop:cross],
  [prop:PP] + sandwich, and `LocalHypsEventually cϱ P` (the taper facts [eq:psidef],
  [eq:abdef], [eq:gbounds], [eq:Phi2FT], [lem:poisson] … for the concrete φ — proved in
  `Zeta23/PrimeSideA/Bridge.lean` from Taper.lean / Poisson.lean);
* `thm_traces_of_localHyps : … → ThmTracesHyp P Z`.
-/

noncomputable section

open Real Filter Topology MeasureTheory
open scoped BigOperators ArithmeticFunction

namespace Zeta23

namespace PrimeSide

open PaperParams

variable (P : Params)

/-- The concrete `Data P`: the actual prime-side traces, 𝓜-terms, `∫_T^{2T} μ²` and
`Σ_{n≤X} Λ(n)²/n g(log n)`, and `N(T,2T)` of the zero configuration `Z`. -/
def concreteData (Z : ZeroConfig) : Data P where
  aT := P.a
  bT := P.b
  trG := P.trGtilde
  trG2 := P.trGtildeSq
  Ncnt := fun T => (Z.N T (2 * T) : ℝ)
  Mtot := fun T => MtotalA (P.toSetting T) (P.localFun T)
  Mmumu := fun T => Mform (P.PhiR T) T mu mu
  MPP := fun T => Mform (P.PhiR T) T (PX (P.X T)) (PX (P.X T))
  MmuP := fun T => Mform (P.PhiR T) T mu (PX (P.X T))
  MmuPi := fun T => Mform (P.PhiR T) T mu (PiX (P.X T))
  MPPi := fun T => Mform (P.PhiR T) T (PX (P.X T)) (PiX (P.X T))
  MPiPi := fun T => Mform (P.PhiR T) T (PiX (P.X T)) (PiX (P.X T))
  intMu2 := fun T => ∫ τ in T..(2 * T), mu τ ^ 2
  sumL2g := fun T => sumA2g (P.X T) (P.g T)

variable {P}

/-- From H-RvM (`C log T` form) to the `l`-form used by the assembly: `log T ≤ 2 l` eventually. -/
lemma rvm_evBound {Z : ZeroConfig} (hR : RiemannVonMangoldt Z) :
    EvBound (fun T => (Z.N T (2 * T) : ℝ) - T * ell1 T / (2 * π)) l := by
  obtain ⟨C, T₀, hC⟩ := hR.main
  refine ⟨2 * max C 1, by positivity, max T₀ (4 * π ^ 2), fun T hT => ?_⟩
  have hT₀ : T₀ ≤ T := (le_max_left _ _).trans hT
  have hT4 : 4 * π ^ 2 ≤ T := (le_max_right _ _).trans hT
  have hπ := Real.pi_pos
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT4
  have h1 := hC T hT₀
  have h2 : T / (2 * π) * ell1 T = T * ell1 T / (2 * π) := by ring
  rw [h2] at h1
  -- log T ≤ 2 l T  ⟺  log T ≤ 2 log T − 2 log(2π)  ⟺  2 log (2π) ≤ log T ⟺ (2π)² ≤ T
  have hl : Real.log T ≤ 2 * l T := by
    unfold l
    rw [Real.log_div hT0.ne' (by positivity)]
    have : Real.log ((2 * π) ^ 2) ≤ Real.log T :=
      Real.log_le_log (by positivity) (by nlinarith only [hT4])
    rw [Real.log_pow] at this
    push_cast at this
    linarith only [this]
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg (by nlinarith only [hT4, hπ, Real.pi_gt_three])
  calc |(Z.N T (2 * T) : ℝ) - T * ell1 T / (2 * π)| ≤ C * Real.log T := h1
    _ ≤ max C 1 * Real.log T := mul_le_mul_of_nonneg_right (le_max_left _ _) hlog0
    _ ≤ max C 1 * (2 * l T) := mul_le_mul_of_nonneg_left hl (by positivity)
    _ = 2 * max C 1 * l T := by ring

/-- **`Facts` for the concrete data.**  Inputs: `P.Valid`; `PaperInputs Z` (only H-RvM, H-Γ,
H-cheb, H-MV are used); the taper facts eventually (`LocalHypsEventually`).  The §5 sub-results are
proved elsewhere in the repository. -/
theorem concreteFacts {cϱ : ℝ} {Z : ZeroConfig} (hP : P.Valid) (inp : PaperInputs Z)
    (hLoc : LocalHypsEventually cϱ P) : Facts (concreteData P Z) := by
  have hlam : 0 < P.lam ∧ P.lam ≤ 1 := ⟨hP.lam_pos, hP.lam_le_one⟩
  have hΓ := inp.Gamma
  have hcheb := inp.cheb
  -- the regime, for majorant nonnegativity
  have hreg : ∀ᶠ T in atTop, 0 ≤ T ∧ 0 ≤ l T ∧ 0 ≤ Real.log (l T) ∧ 0 ≤ P.L T ∧ 0 ≤ P.X T := by
    filter_upwards [eventually_ge_atTop 1, eventually_l_ge 1, eventually_log_l_ge 1,
      eventually_L_ge P hP.lam_pos 1, eventually_one_le_X P hP.lam_pos] with T h1 h2 h3 h4 h5
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨T₀, hT₀⟩ := id hLoc
  -- the §5 sub-results, specialised to the concrete data (EventuallyAt → EvBound)
  have e_ends := evBound_of_eventuallyAt hLoc ((PrimeSide.lem_ends cϱ P.lam hΓ hcheb hlam).imp fun _ h => h.to_eventuallyAt) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact mul_nonneg (mul_nonneg (mul_nonneg hL hl) hlog) (add_nonneg (sq_nonneg _) hX))
  have e_mumu := evBound_of_eventuallyAt hLoc ((PrimeSide.prop_mumu cϱ P.lam hΓ hcheb hlam).imp fun _ h => h.to_eventuallyAt) (by
    filter_upwards [hreg, eventually_L_ge P hP.lam_pos 1] with T ⟨hT, hl, hlog, hL, hX⟩ hL1
    exact mul_nonneg (sq_nonneg _) (Real.log_nonneg hL1))
  have e_PP := evBound_of_eventuallyAt hLoc
    ((PrimeSide.prop_PP (cϱ := cϱ) (lam := P.lam) hcheb inp.MV hlam).imp fun _ h => h.to_eventuallyAt) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact mul_nonneg (sq_nonneg _) hX)
  have e_muP := evBound_of_eventuallyAt hLoc ((PrimeSide.prop_cross_muP cϱ P.lam hΓ hcheb hlam).imp fun _ h => h.to_eventuallyAt) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact mul_nonneg hl (Real.sqrt_nonneg _))
  have e_muPi := evBound_of_eventuallyAt hLoc ((PrimeSide.prop_cross_muPi cϱ P.lam hΓ hcheb hlam).imp fun _ h => h.to_eventuallyAt) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact mul_nonneg (mul_nonneg hl hL) (Real.sqrt_nonneg _))
  have e_PPi := evBound_of_eventuallyAt hLoc ((PrimeSide.prop_cross_PPi cϱ P.lam hΓ hcheb hlam).imp fun _ h => h.to_eventuallyAt) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact mul_nonneg hL hX)
  have e_PiPi := evBound_of_eventuallyAt hLoc ((PrimeSide.prop_cross_PiPi cϱ P.lam hΓ hcheb hlam).imp fun _ h => h.to_eventuallyAt) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact div_nonneg (mul_nonneg hL hX) hT)
  refine ⟨hP.lam_pos, hP.lam_le_one, hP.one_le_w, ?abdef, rvm_evBound inp.RvM, ?muints2,
    ?prop_trace, ?lem_ends, ?Msplit, ?prop_mumu, ?prop_PP, ?sum_lower, ?sum_upper,
    ?cross_muP, ?cross_muPi, ?cross_PPi, ?cross_PiPi⟩
  case abdef =>
    filter_upwards [eventually_ge_atTop T₀] with T hT
    have hF := hT₀ T hT
    exact ⟨hF.b_lower, hF.b_le_a, hF.a_le_one⟩
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
    obtain ⟨C, T₂, hC⟩ := PrimeSide.prop_trace cϱ P.lam hΓ hcheb hlam A
    refine ⟨max C 1, by positivity, max T₀ (max T₁ T₂), fun T hT => ?_⟩
    have h0 : T₀ ≤ T := (le_max_left _ _).trans hT
    have h1 : T₁ ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
    have h2 : T₂ ≤ T := ((le_max_right _ _).trans (le_max_right _ _)).trans hT
    have hF := hT₀ T h0
    have := hC (P.toSetting T) (P.localFun T) rfl h2 hF.toCore (Z.N T (2 * T) : ℝ) (hN T h1)
    rw [trGtA_concrete] at this
    refine this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    exact mul_nonneg hF.L_pos.le (Real.sqrt_nonneg _)
  case lem_ends =>
    exact e_ends.congr_left (Eventually.of_forall fun T => by
      show P.trGtildeSq T - _ = _; rw [← trGt2A_concrete]; rfl)
  case Msplit =>
    filter_upwards [eventually_ge_atTop T₀] with T hT
    exact eq_Msplit cϱ hΓ (P.toSetting T) (P.localFun T) (hT₀ T hT).toCore
  case prop_mumu => exact e_mumu
  case prop_PP => exact e_PP
  case sum_lower =>
    obtain ⟨C, T₁, hC⟩ := PrimeSide.sum_a2g_lower (cϱ := cϱ) (lam := P.lam) hcheb hlam
    refine ⟨max C 1, by positivity, max T₀ T₁, fun T hT => ?_⟩
    have h0 : T₀ ≤ T := (le_max_left _ _).trans hT
    have h1 : T₁ ≤ T := (le_max_right _ _).trans hT
    have key := hC (P.toSetting T) (P.localFun T) rfl h1 (hT₀ T h0)
    simp only [Params.toSetting_L, Params.toSetting_X, Params.toSetting_w, Params.localFun_g] at key
    show |min (sumA2g (P.X T) (P.g T) - (P.L T - 2 * P.w) ^ 3 / 6) 0| ≤ max C 1 * P.L T ^ 2
    rw [abs_of_nonpos (min_le_right _ _)]
    have hCL : C * P.L T ^ 2 ≤ max C 1 * P.L T ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    have hpos : 0 ≤ max C 1 * P.L T ^ 2 := by positivity
    rcases min_cases (sumA2g (P.X T) (P.g T) - (P.L T - 2 * P.w) ^ 3 / 6) 0 with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; linarith
    · rw [h]; simpa using hpos
  case sum_upper =>
    obtain ⟨C, T₁, hC⟩ := PrimeSide.sum_a2g_upper (cϱ := cϱ) (lam := P.lam) hcheb hlam
    refine ⟨max C 1, by positivity, max T₀ T₁, fun T hT => ?_⟩
    have h0 : T₀ ≤ T := (le_max_left _ _).trans hT
    have h1 : T₁ ≤ T := (le_max_right _ _).trans hT
    have key := hC (P.toSetting T) (P.localFun T) rfl h1 (hT₀ T h0).toCore
    simp only [Params.toSetting_L, Params.toSetting_X, Params.localFun_g] at key
    show |max (sumA2g (P.X T) (P.g T) - P.L T ^ 3 / 6) 0| ≤ max C 1 * P.L T ^ 2
    rw [abs_of_nonneg (le_max_right _ _)]
    have hCL : C * P.L T ^ 2 ≤ max C 1 * P.L T ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    have hpos : 0 ≤ max C 1 * P.L T ^ 2 := by positivity
    exact max_le (by linarith) hpos
  case cross_muP => exact e_muP
  case cross_muPi => exact e_muPi
  case cross_PPi => exact e_PPi
  case cross_PiPi => exact e_PiPi

/-- **[thm:traces] for the concrete prime-side data**: the hypothesis `ThmTracesHyp P Z` of
`PrimeSideTemp.lean` follows from `P.Valid`, the published inputs `PaperInputs Z`, and the taper
facts for the concrete φ. -/
theorem thm_traces_of_localHyps {cϱ : ℝ} {Z : ZeroConfig} (hP : P.Valid) (inp : PaperInputs Z)
    (hLoc : LocalHypsEventually cϱ P) : ThmTracesHyp P Z :=
  tracesBounds_of_facts (concreteFacts hP inp hLoc)

end PrimeSide

end Zeta23

end
