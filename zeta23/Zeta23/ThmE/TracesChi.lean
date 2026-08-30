/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization of the paper
"More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/
import Zeta23.ThmE.TracesHypChi
import Zeta23.ThmE.PrimeSideChi
import Zeta23.ThmE.PPChi
import Zeta23.ThmE.MuMuChi
import Zeta23.ThmE.CrossMuPChi
import Zeta23.PrimeSideB
import Zeta23.PrimeSideB.Concrete
import Zeta23.PrimeSideA.Bridge

/-!
# [thm:traces] for L(s,chi) — the E3 assembly

Mirror of Zeta23/PrimeSideB.lean (abstract Facts → TracesBounds assembly) and
Zeta23/PrimeSideB/Traces.lean (concrete instantiation) for a Dirichlet character:
ell1 ↦ ell1q q, nu_X ↦ nu_{X,chi} = mu_{kappa,q} + P_{X,c} (no pole term: [eq:Msplit] has three
terms), [prop:PP] main sum ↦ sumA2gCoprime.  The real-variable pointwise lemmas tr2_pointwise and
ratio_pointwise (PrimeSideB.lean) are reused verbatim — they take the density-log as a free real,
and ell1q slots in (l ≤ ell1q for q ≥ 1).  Constants may depend on q (q fixed in [thm:E]; the
q-uniformity question for [rem:otherL](i) is not addressed in this file).

Inputs: prop_trace_chi, eq_Msplit_chi (PrimeSideChi.lean);
prop_mumu_chi (MuMuChi.lean); prop_cross_muP_chi_proved (CrossMuPChi.lean);
prop_PP_chi + sumA2gCoprime sandwich (PPChi.lean);
lem_ends_chi (via the nu-generic lem:ends).
-/

noncomputable section

open Real Filter Topology MeasureTheory
open scoped BigOperators ArithmeticFunction

namespace Zeta23
namespace ThmE

open Zeta23.PaperParams Zeta23.PrimeSide

/-- l ≤ ell1q q T for q ≥ 1, T > 0. -/
lemma l_le_ell1q {q : ℕ} (hq : 1 ≤ q) {T : ℝ} (hT : 0 < T) : Zeta23.l T ≤ ell1q q T := by
  unfold ell1q Zeta23.l
  have h1 : Real.log (T / (2 * π)) ≤ Real.log (q * T / (2 * π)) := by
    apply Real.log_le_log (by positivity)
    have hq' : (1:ℝ) ≤ q := by exact_mod_cast hq
    rw [div_le_div_iff_of_pos_right (by positivity)]
    nlinarith
  have h2 : 0 < 2 * Real.log 2 - 1 := Zeta23.PaperParams.two_log_two_sub_one_pos
  linarith

/-- The data of the chi-[thm:traces] assembly (mirror of PrimeSide.Data; no Pi-terms). -/
structure DataChi (P : Params) where
  aT : ℝ → ℝ
  bT : ℝ → ℝ
  trG : ℝ → ℝ
  trG2 : ℝ → ℝ
  Ncnt : ℝ → ℝ
  Mtot : ℝ → ℝ
  Mmumu : ℝ → ℝ
  MPP : ℝ → ℝ
  MmuP : ℝ → ℝ
  intMu2 : ℝ → ℝ
  sumL2gq : ℝ → ℝ

variable {P : Params} {q : ℕ} (D : DataChi P)

/-- Hypotheses of the chi-assembly = conclusions of the §5-chi sub-results (mirror of
PrimeSide.Facts; [thm:E] proof (iii)). -/
structure FactsChi (q : ℕ) (D : DataChi P) : Prop where
  lam_pos : 0 < P.lam
  lam_le_one : P.lam ≤ 1
  one_le_w : 1 ≤ P.w
  one_le_q : 1 ≤ q
  abdef : ∀ᶠ T in atTop, 1 - 2 * P.w / P.L T ≤ D.bT T ∧ D.bT T ≤ D.aT T ∧ D.aT T ≤ 1
  rvm : EvBound (fun T => D.Ncnt T - T * ell1q q T / (2 * π)) Zeta23.l
  muints2 : EvBound (fun T => D.intMu2 T - T * ell1q q T ^ 2 / (4 * π ^ 2))
      (fun T => T * ell1q q T ^ 2 / (4 * π ^ 2) / Zeta23.l T ^ 2)
  prop_trace : EvBound (fun T => D.trG T - D.aT T * P.L T * D.Ncnt T)
      (fun T => P.L T * Real.sqrt (P.X T))
  lem_ends : EvBound (fun T => D.trG2 T - D.Mtot T)
      (fun T => P.L T * Zeta23.l T * Real.log (Zeta23.l T) * (Zeta23.l T ^ 2 + P.X T))
  Msplit : ∀ᶠ T in atTop, D.Mtot T = D.Mmumu T + D.MPP T + 2 * D.MmuP T
  prop_mumu : EvBound (fun T => D.Mmumu T - 2 * π * D.bT T * P.L T * D.intMu2 T)
      (fun T => Zeta23.l T ^ 2 * Real.log (P.L T))
  prop_PP : EvBound (fun T => D.MPP T - T / π * D.sumL2gq T) (fun T => P.L T ^ 2 * P.X T)
  sum_lower : EvBound (fun T => min (D.sumL2gq T - (P.L T - 2 * P.w) ^ 3 / 6) 0)
      (fun T => P.L T ^ 2)
  sum_upper : EvBound (fun T => max (D.sumL2gq T - P.L T ^ 3 / 6) 0) (fun T => P.L T ^ 2)
  cross_muP : EvBound D.MmuP (fun T => Zeta23.l T * Real.sqrt (P.X T))

section assembly
variable {D} (h : FactsChi q D)
include h

theorem tr1_chi : EvBound (fun T => D.trG T - D.aT T * P.L T * D.Ncnt T)
    (fun T => P.L T * Real.sqrt (P.X T)) := h.prop_trace

lemma Ncnt_lower_chi : ∀ᶠ T in atTop, T * Zeta23.l T / (4 * π) ≤ D.Ncnt T := by
  obtain ⟨A, hA, hN⟩ := h.rvm.eventually_le
  filter_upwards [hN, eventually_ge_atTop (4 * π * A), eventually_l_ge 0, eventually_gt_atTop 0]
    with T hN hTA hl hT0
  have hπ := Real.pi_pos
  have hle := l_le_ell1q h.one_le_q hT0
  have h1 : -(A * Zeta23.l T) ≤ D.Ncnt T - T * ell1q q T / (2 * π) := (abs_le.mp hN).1
  have h2 : T * Zeta23.l T ≤ T * ell1q q T :=
    mul_le_mul_of_nonneg_left hle (by linarith)
  have h3 : T * Zeta23.l T / (2 * π) ≤ T * ell1q q T / (2 * π) :=
    div_le_div_of_nonneg_right h2 (by positivity)
  have h4 : T * Zeta23.l T / (4 * π) = T * Zeta23.l T / (2 * π) - T * Zeta23.l T / (4 * π) := by
    ring
  have h5 : A * Zeta23.l T ≤ T * Zeta23.l T / (4 * π) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  linarith

lemma T_le_Ncnt_chi : ∀ᶠ T in atTop, T ≤ 4 * π * D.Ncnt T := by
  filter_upwards [Ncnt_lower_chi h, eventually_l_ge 1, eventually_ge_atTop 0] with T hN hl hT
  have hπ := Real.pi_pos
  have : T * Zeta23.l T ≤ 4 * π * D.Ncnt T := by rw [div_le_iff₀ (by positivity)] at hN; linarith
  nlinarith

lemma Ncnt_pos_chi : ∀ᶠ T in atTop, 0 < D.Ncnt T := by
  filter_upwards [Ncnt_lower_chi h, eventually_l_ge 1, eventually_ge_atTop 1] with T hN hl hT
  have hπ := Real.pi_pos
  have h0 : 0 < T * Zeta23.l T / (4 * π) := by positivity
  linarith

theorem tr1'_chi : EvBound (fun T => D.trG T - P.L T * D.Ncnt T)
    (fun T => P.calE T * (P.L T * D.Ncnt T)) := by
  obtain ⟨C₁, hC₁, h1⟩ := h.prop_trace.eventually_le
  have hlam := h.lam_pos
  have hw : 0 ≤ P.w := by linarith [h.one_le_w]
  refine EvBound.of_eventually_le (c := 4 * π * C₁ + 2) (by positivity) ?_
  filter_upwards [h1, h.abdef, calE_ge_w_div_L hlam hw, calE_ge_rpow hlam hw,
    calE_nonneg_eventually hlam hw, T_le_Ncnt_chi h, Ncnt_pos_chi h, eventually_ge_atTop 1,
    eventually_L_ge P hlam 1] with T h1 hab hEw hEr hE0 hTN hN0 hT1 hL1
  obtain ⟨hb1, hba, ha1⟩ := hab
  have hT0 : 0 < T := by linarith
  have hL0 : 0 ≤ P.L T := by linarith
  set N := D.Ncnt T
  set L := P.L T
  set E := P.calE T
  have hLN : 0 ≤ L * N := mul_nonneg hL0 hN0.le
  have hA : |D.aT T * L * N - L * N| ≤ 2 * E * (L * N) := by
    have e : D.aT T * L * N - L * N = -((1 - D.aT T) * (L * N)) := by ring
    rw [e, abs_neg, abs_of_nonneg (mul_nonneg (by linarith) hLN)]
    have h2 : 1 - D.aT T ≤ 2 * E := by
      have e2 : 2 * P.w / L = 2 * (P.w / L) := by ring
      linarith
    exact mul_le_mul_of_nonneg_right h2 hLN
  have hB : C₁ * (L * Real.sqrt (P.X T)) ≤ 4 * π * C₁ * (E * (L * N)) := by
    have hs : Real.sqrt (P.X T) ≤ T ^ (P.lam / 2 - 1) * T := by
      rw [rpow_half_sub_one_mul hT0]; exact sqrt_X_le_rpow P hlam hT0
    have hs2 : T ^ (P.lam / 2 - 1) * T ≤ E * (4 * π * N) :=
      mul_le_mul hEr hTN hT0.le hE0
    calc C₁ * (L * Real.sqrt (P.X T)) ≤ C₁ * (L * (E * (4 * π * N))) := by
          gcongr; exact hs.trans hs2
      _ = 4 * π * C₁ * (E * (L * N)) := by ring
  calc |D.trG T - L * N|
      ≤ |D.trG T - D.aT T * L * N| + |D.aT T * L * N - L * N| := abs_sub_le _ _ _
    _ ≤ C₁ * (L * Real.sqrt (P.X T)) + 2 * E * (L * N) := add_le_add h1 hA
    _ ≤ 4 * π * C₁ * (E * (L * N)) + 2 * E * (L * N) := by linarith
    _ = (4 * π * C₁ + 2) * (E * (L * N)) := by ring

lemma regime_chi : ∀ᶠ T in atTop, 1 ≤ T ∧ 1 ≤ Zeta23.l T ∧ 1 ≤ Real.log (Zeta23.l T) ∧ 1 ≤ P.L T ∧
    1 ≤ P.X T ∧ P.L T ≤ Zeta23.l T ∧ P.X T ≤ T := by
  have hlam := h.lam_pos
  filter_upwards [eventually_ge_atTop 1, eventually_l_ge 1, eventually_log_l_ge 1,
    eventually_L_ge P hlam 1, eventually_one_le_X P hlam, eventually_X_le_T P hlam h.lam_le_one]
    with T h1 h2 h3 h4 h5 h6
  exact ⟨h1, h2, h3, h4, h5, L_le_l P h.lam_le_one (by linarith), h6⟩

/-- [eq:tr2] first form for chi (three-term Msplit). -/
theorem tr2_first_chi : EvBound
    (fun T => D.trG2 T - (2 * π * D.bT T * P.L T * D.intMu2 T + T / π * D.sumL2gq T))
    (fun T => P.L T * Zeta23.l T * Real.log (Zeta23.l T) * (Zeta23.l T ^ 2 + P.X T)) := by
  have e4 : EvBound (fun T => D.MPP T - T / π * D.sumL2gq T)
      (fun T => P.L T * Zeta23.l T * Real.log (Zeta23.l T) * (Zeta23.l T ^ 2 + P.X T)) := by
    refine h.prop_PP.mono_right' one_pos ?_
    filter_upwards [regime_chi h] with T ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩
    calc P.L T ^ 2 * P.X T = P.L T * P.L T * 1 * P.X T := by ring
      _ ≤ P.L T * Zeta23.l T * Real.log (Zeta23.l T) * (Zeta23.l T ^ 2 + P.X T) := by gcongr; nlinarith
      _ = 1 * (P.L T * Zeta23.l T * Real.log (Zeta23.l T) * (Zeta23.l T ^ 2 + P.X T)) := (one_mul _).symm
  have e3 : EvBound (fun T => D.Mmumu T - 2 * π * D.bT T * P.L T * D.intMu2 T)
      (fun T => P.L T * Zeta23.l T * Real.log (Zeta23.l T) * (Zeta23.l T ^ 2 + P.X T)) := by
    refine h.prop_mumu.mono_right' one_pos ?_
    filter_upwards [regime_chi h] with T ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩
    have hlogL : Real.log (P.L T) ≤ Real.log (Zeta23.l T) := Real.log_le_log (by linarith) hLl
    have hlogL0 : 0 ≤ Real.log (P.L T) := Real.log_nonneg hL
    calc Zeta23.l T ^ 2 * Real.log (P.L T) ≤ Zeta23.l T ^ 2 * Real.log (Zeta23.l T) := by gcongr
      _ = 1 * Zeta23.l T * Real.log (Zeta23.l T) * Zeta23.l T := by ring
      _ ≤ P.L T * Zeta23.l T * Real.log (Zeta23.l T) * (Zeta23.l T ^ 2 + P.X T) := by gcongr; nlinarith
      _ = _ := (one_mul _).symm
  have hsqrtX : ∀ᶠ T in atTop, Real.sqrt (P.X T) ≤ P.X T := by
    filter_upwards [regime_chi h] with T ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have e5 : EvBound D.MmuP
      (fun T => P.L T * Zeta23.l T * Real.log (Zeta23.l T) * (Zeta23.l T ^ 2 + P.X T)) := by
    refine h.cross_muP.mono_right' one_pos ?_
    filter_upwards [regime_chi h, hsqrtX] with T ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩ hs
    calc Zeta23.l T * Real.sqrt (P.X T) ≤ Zeta23.l T * P.X T := by gcongr
      _ = 1 * Zeta23.l T * 1 * (0 + P.X T) := by ring
      _ ≤ P.L T * Zeta23.l T * Real.log (Zeta23.l T) * (Zeta23.l T ^ 2 + P.X T) := by gcongr; nlinarith
      _ = _ := (one_mul _).symm
  have S := h.lem_ends.add (e3.add (e4.add (e5.const_mul 2)))
  refine S.congr_left ?_
  filter_upwards [h.Msplit] with T hM
  rw [hM]; ring

/-- [eq:tr2], second form for chi. -/
theorem tr2_chi : EvBound (fun T => D.trG2 T - mainTr2Chi P q T)
    (fun T => P.calE T * mainTr2Chi P q T) := by
  have hlam := h.lam_pos
  have hw1 := h.one_le_w
  have hw : 0 ≤ P.w := by linarith
  obtain ⟨CR, hCR, hR⟩ := (tr2_first_chi h).eventually_le
  obtain ⟨Cμ, hCμ, hμ⟩ := h.muints2.eventually_le
  obtain ⟨Cu, hCu, hu⟩ := h.sum_upper.eventually_le
  obtain ⟨Cl, hCl, hlo⟩ := h.sum_lower.eventually_le
  refine EvBound.of_eventually_le
    (c := 2 * π * CR + Cμ + 2 + 6 * (Cu + Cl + 2 * P.w)) (by positivity) ?_
  filter_upwards [hR, hμ, hu, hlo, h.abdef, regime_chi h, calE_ge_w_div_L hlam hw,
    calE_ge_mid hlam hw, calE_nonneg_eventually hlam hw, eventually_L_ge P hlam (2 * P.w),
    eventually_gt_atTop 0]
    with T hR hμ hu hlo hab hreg hEw hEmid hE0 hL2w hT0
  obtain ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩ := hreg
  obtain ⟨hb1, hba, ha1⟩ := hab
  have hSup : D.sumL2gq T - P.L T ^ 3 / 6 ≤ Cu * P.L T ^ 2 := by
    rw [abs_of_nonneg (le_max_right _ _)] at hu
    exact (le_max_left _ _).trans hu
  have hSlo : -(Cl * P.L T ^ 2) ≤ D.sumL2gq T - (P.L T - 2 * P.w) ^ 3 / 6 :=
    (abs_le.mp hlo).1.trans (min_le_left _ _)
  exact tr2_pointwise T (P.L T) (ell1q q T) (Zeta23.l T) (P.X T) (P.calE T) (D.sumL2gq T)
    (D.intMu2 T) (D.bT T) (D.trG2 T) P.w CR Cμ Cu Cl hT hL hl hlog hX
    (l_le_ell1q h.one_le_q hT0) hLl hw1 hL2w hb1 (hba.trans ha1)
    hE0 hEw hEmid hCR.le hCμ.le hCu.le hCl.le hR hμ hSup hSlo

/-- [eq:ratio] for chi. -/
theorem ratio_chi : EvBound
    (fun T => D.trG T ^ 2 / D.trG2 T - Ffun (lam1q P q T) * D.Ncnt T)
    (fun T => P.calE T * (Ffun (lam1q P q T) * D.Ncnt T)) := by
  have hlam := h.lam_pos
  have hlam1 := h.lam_le_one
  have hw : 0 ≤ P.w := by linarith [h.one_le_w]
  obtain ⟨C₁, hC₁, h1⟩ := (tr1'_chi h).eventually_le
  obtain ⟨C₂, hC₂, h2⟩ := (tr2_chi h).eventually_le
  obtain ⟨A, hA, hN⟩ := h.rvm.eventually_le
  have hcal := calE_tendsto_zero hlam hlam1 hw
  have hs1 : ∀ᶠ T in atTop, C₁ * P.calE T ≤ 1 / 2 := by
    filter_upwards [hcal.eventually (Iio_mem_nhds (show (0:ℝ) < 1 / (2 * C₁) by positivity))]
      with T hT
    rw [lt_div_iff₀ (by positivity)] at hT
    linarith
  have hs2 : ∀ᶠ T in atTop, C₂ * P.calE T ≤ 1 / 2 := by
    filter_upwards [hcal.eventually (Iio_mem_nhds (show (0:ℝ) < 1 / (2 * C₂) by positivity))]
      with T hT
    rw [lt_div_iff₀ (by positivity)] at hT
    linarith
  refine EvBound.of_eventually_le (c := 2 * (2 * π * A + 5 * C₁ + C₂)) (by positivity) ?_
  filter_upwards [h1, h2, hN, hs1, hs2, regime_chi h, calE_ge_rpow hlam hw,
    calE_nonneg_eventually hlam hw, Ncnt_pos_chi h, eventually_ge_atTop (2 * π * A),
    eventually_gt_atTop 0]
    with T h1 h2 hN hs1 hs2 hreg hEr hE0 hN0 hTA hT0
  obtain ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩ := hreg
  have hle := l_le_ell1q h.one_le_q hT0
  have hET : 1 / T ≤ P.calE T := by
    refine le_trans ?_ hEr
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  exact ratio_pointwise T (P.L T) (ell1q q T) (Zeta23.l T) (P.calE T) (D.Ncnt T) (D.trG T)
    (D.trG2 T) A C₁ C₂ hT (by linarith) (hl.trans hle) hle hN0 hE0 hET hA.le hC₁.le
    hC₂.le hs1 hs2 hTA h1 h2 hN

/-- [thm:traces] for chi, assembled. -/
theorem tracesBoundsChi_of_factsChi : TracesBoundsChi P q D.aT D.trG D.trG2 D.Ncnt where
  tr1 := tr1_chi h
  tr1' := tr1'_chi h
  tr2 := tr2_chi h
  ratio := ratio_chi h

end assembly

/-! ## Concrete instantiation -/

section Concrete
variable (P : Params) (κ q : ℕ) (c : ℕ → ℂ)

/-- rfl-bridges between the abstract-taper chi-quantities and the concrete ones. -/
lemma GentryChiA_concrete (T : ℝ) (k l : ℤ) :
    GentryChiA κ q c (P.toSetting T) (P.localFun T) k l = GentryChi P κ q c T k l := rfl
lemma trGtChiA_concrete (T : ℝ) :
    trGtChiA κ q c (P.toSetting T) (P.localFun T) = trGtildeChi P κ q c T := rfl
lemma trGt2ChiA_concrete (T : ℝ) :
    trGt2ChiA κ q c (P.toSetting T) (P.localFun T) = trGtildeSqChi P κ q c T := rfl

/-- The concrete chi-data. -/
def concreteDataChi (Z : ZeroConfig) : DataChi P where
  aT := P.a
  bT := P.b
  trG := trGtildeChi P κ q c
  trG2 := trGtildeSqChi P κ q c
  Ncnt := fun T => (Z.N T (2 * T) : ℝ)
  Mtot := fun T => MtotalChiA κ q c (P.toSetting T) (P.localFun T)
  Mmumu := fun T => Mform (P.PhiR T) T (muq κ q) (muq κ q)
  MPP := fun T => Mform (P.PhiR T) T (PXc c (P.X T)) (PXc c (P.X T))
  MmuP := fun T => Mform (P.PhiR T) T (muq κ q) (PXc c (P.X T))
  intMu2 := fun T => ∫ τ in T..(2 * T), muq κ q τ ^ 2
  sumL2gq := fun T => sumA2gCoprime q (P.X T) (P.g T)

variable {P κ q c}

/-- H-RvM(chi) in the l-majorant form. -/
lemma rvm_evBound_chi {Z : ZeroConfig} (hR : RiemannVonMangoldtChi q Z) :
    EvBound (fun T => (Z.N T (2 * T) : ℝ) - T * ell1q q T / (2 * π)) Zeta23.l := by
  obtain ⟨C, T₀, hC⟩ := hR.main
  refine ⟨2 * max C 1, by positivity, max T₀ (4 * π ^ 2), fun T hT => ?_⟩
  have hT₀ : T₀ ≤ T := (le_max_left _ _).trans hT
  have hT4 : 4 * π ^ 2 ≤ T := (le_max_right _ _).trans hT
  have hπ := Real.pi_pos
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT4
  have h1 := hC T hT₀
  have h2 : T / (2 * π) * ell1q q T = T * ell1q q T / (2 * π) := by ring
  rw [h2] at h1
  have hl : Real.log T ≤ 2 * Zeta23.l T := by
    unfold Zeta23.l
    rw [Real.log_div hT0.ne' (by positivity)]
    have h3 : Real.log ((2 * π) ^ 2) ≤ Real.log T :=
      Real.log_le_log (by positivity) (by nlinarith only [hT4])
    rw [Real.log_pow] at h3
    push_cast at h3
    linarith only [h3]
  have hlog0 : 0 ≤ Real.log T := Real.log_nonneg (by nlinarith only [hT4, hπ, Real.pi_gt_three])
  calc |(Z.N T (2 * T) : ℝ) - T * ell1q q T / (2 * π)| ≤ C * Real.log T := h1
    _ ≤ max C 1 * Real.log T := mul_le_mul_of_nonneg_right (le_max_left _ _) hlog0
    _ ≤ max C 1 * (2 * Zeta23.l T) := mul_le_mul_of_nonneg_left hl (by positivity)
    _ = 2 * max C 1 * Zeta23.l T := by ring

set_option maxHeartbeats 1600000 in
/-- FactsChi for the concrete data, from the chi-inputs together with the taper facts
(including lem_ends_chi). -/
theorem concreteFactsChi {cϱ : ℝ} {Z : ZeroConfig} (hP : P.Valid) (hq : 1 ≤ q)
    (hcu : CoeffUnimodular q c) (inp : PaperInputsChi κ q c Z)
    (hLoc : LocalHypsEventually cϱ P) : FactsChi q (concreteDataChi P κ q c Z) := by
  have hlam : 0 < P.lam ∧ P.lam ≤ 1 := ⟨hP.lam_pos, hP.lam_le_one⟩
  have hΓq := inp.Gamma
  have hcheb := inp.cheb
  have hc : CoeffOK q c := hcu.toCoeffOK
  have hreg : ∀ᶠ T in atTop, 0 ≤ T ∧ 0 ≤ Zeta23.l T ∧ 0 ≤ Real.log (Zeta23.l T) ∧ 0 ≤ P.L T
      ∧ 0 ≤ P.X T := by
    filter_upwards [eventually_ge_atTop 1, eventually_l_ge 1, eventually_log_l_ge 1,
      eventually_L_ge P hP.lam_pos 1, eventually_one_le_X P hP.lam_pos] with T h1 h2 h3 h4 h5
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩
  obtain ⟨T₀, hT₀⟩ := id hLoc
  have e_ends := evBound_of_eventuallyAt hLoc
    ((lem_ends_chi (κ := κ) (q := q) (c := c) (cϱ := cϱ) (lam := P.lam) hΓq hcheb hc hlam hq).imp
      fun _ h => h.to_eventuallyAt) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact mul_nonneg (mul_nonneg (mul_nonneg hL hl) hlog) (add_nonneg (sq_nonneg _) hX))
  have e_mumu := evBound_of_eventuallyAt hLoc
    ((prop_mumu_chi (cϱ := cϱ) (lam := P.lam) hΓq hc hq hlam).imp
      fun _ h => h.to_eventuallyAt) (by
    filter_upwards [hreg, eventually_L_ge P hP.lam_pos 1] with T ⟨hT, hl, hlog, hL, hX⟩ hL1
    exact mul_nonneg (sq_nonneg _) (Real.log_nonneg hL1))
  have e_PP := evBound_of_eventuallyAt hLoc
    ((prop_PP_chi (cϱ := cϱ) (lam := P.lam) hcheb inp.MV hcu hlam).imp
      fun _ h => h.to_eventuallyAt) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact mul_nonneg (sq_nonneg _) hX)
  have e_muP := evBound_of_eventuallyAt hLoc
    ((prop_cross_muP_chi_proved (cϱ := cϱ) (lam := P.lam) hΓq hcheb hc hq hlam).imp
      fun _ h => h.to_eventuallyAt) (by
    filter_upwards [hreg] with T ⟨hT, hl, hlog, hL, hX⟩
    exact mul_nonneg hl (Real.sqrt_nonneg _))
  refine ⟨hP.lam_pos, hP.lam_le_one, hP.one_le_w, hq, ?abdef, rvm_evBound_chi inp.RvM, ?muints2,
    ?prop_trace, ?lem_ends, ?Msplit, ?prop_mumu, ?prop_PP, ?sum_lower, ?sum_upper, ?cross_muP⟩
  case abdef =>
    filter_upwards [eventually_ge_atTop T₀] with T hT
    have hF := hT₀ T hT
    exact ⟨hF.b_lower, hF.b_le_a, hF.a_le_one⟩
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
    obtain ⟨C, T₂, hC⟩ := prop_trace_chi (κ := κ) (q := q) (c := c) (cϱ := cϱ) (lam := P.lam) hΓq hcheb hc hlam A hq
    refine ⟨max C 1, by positivity, max (max T₀ 1) (max T₁ T₂), fun T hT => ?_⟩
    have h0 : T₀ ≤ T := ((le_max_left _ _).trans (le_max_left _ _)).trans hT
    have hT1' : (1:ℝ) ≤ T := ((le_max_right _ _).trans (le_max_left _ _)).trans hT
    have h1 : T₁ ≤ T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
    have h2 : T₂ ≤ T := ((le_max_right _ _).trans (le_max_right _ _)).trans hT
    have hF := hT₀ T h0
    have hT0' : (0:ℝ) < T := by linarith
    have hNT : |(Z.N T (2 * T) : ℝ) - T / (2 * π) * ell1q q T| ≤ A * Real.log T := by
      have hl : Zeta23.l T ≤ Real.log T := by
        unfold Zeta23.l
        rw [Real.log_div hT0'.ne' (by positivity)]
        have : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
        linarith
      have hN' := hN T h1
      simp only at hN'
      rw [show T * ell1q q T / (2 * π) = T / (2 * π) * ell1q q T by ring] at hN'
      calc |(Z.N T (2 * T) : ℝ) - T / (2 * π) * ell1q q T| ≤ A * Zeta23.l T := hN'
        _ ≤ A * Real.log T := mul_le_mul_of_nonneg_left hl hA.le
    have key := hC (P.toSetting T) (P.localFun T) rfl h2 hF.toCore (Z.N T (2 * T) : ℝ) hNT
    rw [trGtChiA_concrete] at key
    refine key.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
    exact mul_nonneg hF.L_pos.le (Real.sqrt_nonneg _)
  case lem_ends =>
    exact e_ends.congr_left (Eventually.of_forall fun T => by
      show trGtildeSqChi P κ q c T - _ = _
      rw [← trGt2ChiA_concrete]
      rfl)
  case Msplit =>
    obtain ⟨T₁, hT₁⟩ := eq_Msplit_chi (κ := κ) (q := q) (c := c) (cϱ := cϱ) (lam := P.lam) hΓq hc hlam
    filter_upwards [eventually_ge_atTop T₀, eventually_ge_atTop T₁] with T h0 h1
    exact hT₁ (P.toSetting T) (P.localFun T) rfl h1 (hT₀ T h0).toCore
  case prop_mumu => exact e_mumu
  case prop_PP => exact e_PP
  case sum_lower =>
    obtain ⟨C, T₁, hC⟩ := sumA2gCoprime_lower (cϱ := cϱ) (lam := P.lam) (q := q) inp.chebq hlam
    refine ⟨max C 1, by positivity, max T₀ T₁, fun T hT => ?_⟩
    have h0 : T₀ ≤ T := (le_max_left _ _).trans hT
    have h1 : T₁ ≤ T := (le_max_right _ _).trans hT
    have key := hC (P.toSetting T) (P.localFun T) rfl h1 (hT₀ T h0)
    simp only [Params.toSetting_L, Params.toSetting_X, Params.toSetting_w, Params.localFun_g] at key
    show |min (sumA2gCoprime q (P.X T) (P.g T) - (P.L T - 2 * P.w) ^ 3 / 6) 0| ≤ max C 1 * P.L T ^ 2
    rw [abs_of_nonpos (min_le_right _ _)]
    have hCL : C * P.L T ^ 2 ≤ max C 1 * P.L T ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    have hpos : 0 ≤ max C 1 * P.L T ^ 2 := by positivity
    rcases min_cases (sumA2gCoprime q (P.X T) (P.g T) - (P.L T - 2 * P.w) ^ 3 / 6) 0 with
      ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; linarith
    · rw [h]; simpa using hpos
  case sum_upper =>
    obtain ⟨C, T₁, hC⟩ := sumA2gCoprime_upper (cϱ := cϱ) (lam := P.lam) (q := q) inp.chebq hlam
    refine ⟨max C 1, by positivity, max T₀ T₁, fun T hT => ?_⟩
    have h0 : T₀ ≤ T := (le_max_left _ _).trans hT
    have h1 : T₁ ≤ T := (le_max_right _ _).trans hT
    have key := hC (P.toSetting T) (P.localFun T) rfl h1 (hT₀ T h0).toCore
    simp only [Params.toSetting_L, Params.toSetting_X, Params.localFun_g] at key
    show |max (sumA2gCoprime q (P.X T) (P.g T) - P.L T ^ 3 / 6) 0| ≤ max C 1 * P.L T ^ 2
    rw [abs_of_nonneg (le_max_right _ _)]
    have hCL : C * P.L T ^ 2 ≤ max C 1 * P.L T ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    have hpos : 0 ≤ max C 1 * P.L T ^ 2 := by positivity
    exact max_le (by linarith) hpos
  case cross_muP => exact e_muP

/-- **[thm:traces] for L(s,χ), concrete.** -/
theorem thm_traces_chi {cϱ : ℝ} {Z : ZeroConfig} (hP : P.Valid) (hq : 1 ≤ q)
    (hcu : CoeffUnimodular q c) (inp : PaperInputsChi κ q c Z)
    (hLoc : LocalHypsEventually cϱ P) : ThmTracesHypChi P κ q c Z :=
  tracesBoundsChi_of_factsChi (concreteFactsChi hP hq hcu inp hLoc)

end Concrete

end ThmE
end Zeta23
