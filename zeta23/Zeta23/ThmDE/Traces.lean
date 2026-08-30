/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmDE/Traces.lean — [eq:ratio-general] for L(s,χ):
the window-general [thm:traces] assembly of Zeta23/ThmD/Traces.lean (moments b, J symbolic; the
[eq:gbounds] sandwich replaced by the §7.1 partial-summation field sumJ) with the Dirichlet-
character changes of Zeta23/ThmE/TracesChi.lean ([thm:E] proof (iii)): ℓ₁ ↦ ℓ_{1,χ}, three-term
[eq:Msplit] (no pole terms), Σ_{(n,q)=1}.  The pointwise real inequalities tr2D_pointwise /
ratioD_pointwise / frhatD_pointwise (Zeta23/ThmD/Traces.lean) are reused VERBATIM with ℓ := ℓ_{1,χ}
(they take the density-log as a free real ≥ l).  Output: Zeta23.ThmDE.TracesBoundsDChi.
-/
import Zeta23.ThmD.Traces
import Zeta23.ThmE.TracesChi
import Zeta23.ThmDE.TracesHyp

noncomputable section

open Real Filter

namespace Zeta23
namespace ThmDE

open ThmD ThmE

/-- the data of the χ-D assembly: TracesChi's DataChi plus the window moment J_T [eq:abJ]. -/
structure DataDChi (P : Params) extends ThmE.DataChi P where
  /-- J := (2/L³) ∫_0^L g(y) y dy [eq:abJ]. -/
  JT : ℝ → ℝ

variable {P : Params} {q : ℕ} (D : DataDChi P)

/-- Hypotheses of the window-general χ-[thm:traces] assembly: ThmE.FactsChi with the sandwich
fields (sum_lower/sum_upper) replaced by sumJ and abdef by ab_range (as in ThmD.FactsD). -/
structure FactsDChi (q : ℕ) (D : DataDChi P) : Prop where
  lam_pos : 0 < P.lam
  lam_le_one : P.lam ≤ 1
  one_le_w : 1 ≤ P.w
  one_le_q : 1 ≤ q
  /-- window-general [eq:abJ] ranges: 1/2 ≤ b ≤ a ≤ 1 and 0 ≤ J ≤ 1 eventually. -/
  ab_range : ∀ᶠ T in atTop,
    1 / 2 ≤ D.bT T ∧ D.bT T ≤ D.aT T ∧ D.aT T ≤ 1 ∧ 0 ≤ D.JT T ∧ D.JT T ≤ 1
  rvm : EvBound (fun T => D.Ncnt T - T * ell1q q T / (2 * π)) l
  muints2 : EvBound (fun T => D.intMu2 T - T * ell1q q T ^ 2 / (4 * π ^ 2))
      (fun T => T * ell1q q T ^ 2 / (4 * π ^ 2) / l T ^ 2)
  prop_trace : EvBound (fun T => D.trG T - D.aT T * P.L T * D.Ncnt T)
      (fun T => P.L T * Real.sqrt (P.X T))
  lem_ends : EvBound (fun T => D.trG2 T - D.Mtot T)
      (fun T => P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T))
  Msplit : ∀ᶠ T in atTop, D.Mtot T = D.Mmumu T + D.MPP T + 2 * D.MmuP T
  prop_mumu : EvBound (fun T => D.Mmumu T - 2 * π * D.bT T * P.L T * D.intMu2 T)
      (fun T => l T ^ 2 * Real.log (P.L T))
  prop_PP : EvBound (fun T => D.MPP T - T / π * D.sumL2gq T) (fun T => P.L T ^ 2 * P.X T)
  /-- the §7.1 partial-summation step for the coprime sum:
  Σ_{n≤X,(n,q)=1} a_n² g(y_n) = (L³/2)·J_T + O_q(L²). -/
  sumJ : EvBound (fun T => D.sumL2gq T - P.L T ^ 3 / 2 * D.JT T) (fun T => P.L T ^ 2)
  cross_muP : EvBound D.MmuP (fun T => l T * Real.sqrt (P.X T))

section assemblyD
variable {D} (h : FactsDChi q D)
include h

private lemma NcntD_lower : ∀ᶠ T in Filter.atTop, T * l T / (4 * π) ≤ D.Ncnt T := by
  obtain ⟨A, hA, hN⟩ := h.rvm.eventually_le
  filter_upwards [hN, Filter.eventually_ge_atTop (4 * π * A), PaperParams.eventually_l_ge 0,
    Filter.eventually_gt_atTop (0:ℝ)] with T hN hTA hl hT0
  have hπ := Real.pi_pos
  have h1 : -(A * l T) ≤ D.Ncnt T - T * ell1q q T / (2 * π) := (abs_le.mp hN).1
  have h2 : T * l T ≤ T * ell1q q T :=
    mul_le_mul_of_nonneg_left (ThmE.l_le_ell1q h.one_le_q hT0) (by linarith)
  have h3 : T * l T / (2 * π) ≤ T * ell1q q T / (2 * π) :=
    div_le_div_of_nonneg_right h2 (by positivity)
  have h4 : T * l T / (4 * π) = T * l T / (2 * π) - T * l T / (4 * π) := by ring
  have h5 : A * l T ≤ T * l T / (4 * π) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  linarith

private lemma T_le_NcntD : ∀ᶠ T in Filter.atTop, T ≤ 4 * π * D.Ncnt T := by
  filter_upwards [NcntD_lower h, PaperParams.eventually_l_ge 1, Filter.eventually_ge_atTop 0]
    with T hN hl hT
  have hπ := Real.pi_pos
  have : T * l T ≤ 4 * π * D.Ncnt T := by
    rw [div_le_iff₀ (by positivity)] at hN
    linarith
  nlinarith

private lemma NcntD_pos : ∀ᶠ T in Filter.atTop, 0 < D.Ncnt T := by
  filter_upwards [NcntD_lower h, PaperParams.eventually_l_ge 1, Filter.eventually_ge_atTop 1]
    with T hN hl hT
  have hπ := Real.pi_pos
  have h0 : (0:ℝ) < T * l T / (4 * π) := by positivity
  linarith

private lemma regimeD : ∀ᶠ T in Filter.atTop, 1 ≤ T ∧ 1 ≤ l T ∧ 1 ≤ Real.log (l T)
    ∧ 1 ≤ P.L T ∧ 1 ≤ P.X T ∧ P.L T ≤ l T ∧ P.X T ≤ T := by
  have hlam := h.lam_pos
  filter_upwards [Filter.eventually_ge_atTop 1, PaperParams.eventually_l_ge 1,
    PaperParams.eventually_log_l_ge 1, PaperParams.eventually_L_ge P hlam 1,
    PaperParams.eventually_one_le_X P hlam,
    PaperParams.eventually_X_le_T P hlam h.lam_le_one] with T h1 h2 h3 h4 h5 h6
  exact ⟨h1, h2, h3, h4, h5, PaperParams.L_le_l P h.lam_le_one (by linarith), h6⟩

/-- the D-form of [eq:tr1]': tr G̃ = a L N (1 + O(𝓔)) — a STAYS (no collapse to 1). -/
private lemma tr1'D : EvBound (fun T => D.trG T - D.aT T * P.L T * D.Ncnt T)
    (fun T => P.calE T * (D.aT T * P.L T * D.Ncnt T)) := by
  obtain ⟨C₁, hC₁, h1⟩ := h.prop_trace.eventually_le
  have hlam := h.lam_pos
  have hw : 0 ≤ P.w := by linarith [h.one_le_w]
  refine EvBound.of_eventually_le (c := 8 * π * C₁) (by positivity) ?_
  filter_upwards [h1, h.ab_range, PaperParams.calE_ge_rpow hlam hw,
    PaperParams.calE_nonneg_eventually hlam hw, T_le_NcntD h, NcntD_pos h,
    Filter.eventually_ge_atTop 1, PaperParams.eventually_L_ge P hlam 1]
    with T h1 hab hEr hE0 hTN hN0 hT1 hL1
  obtain ⟨hb2, hba, ha1, hJ0, hJ1⟩ := hab
  have hT0 : 0 < T := by linarith
  have hL0 : 0 ≤ P.L T := by linarith
  have ha2 : 1 / 2 ≤ D.aT T := le_trans hb2 hba
  have hB : C₁ * (P.L T * Real.sqrt (P.X T))
      ≤ 8 * π * C₁ * (P.calE T * (D.aT T * P.L T * D.Ncnt T)) := by
    have hs : Real.sqrt (P.X T) ≤ T ^ (P.lam / 2 - 1) * T := by
      rw [PaperParams.rpow_half_sub_one_mul hT0]
      exact PaperParams.sqrt_X_le_rpow P hlam hT0
    have hs2 : T ^ (P.lam / 2 - 1) * T ≤ P.calE T * (4 * π * D.Ncnt T) :=
      mul_le_mul hEr hTN hT0.le hE0
    calc C₁ * (P.L T * Real.sqrt (P.X T))
        ≤ C₁ * (P.L T * (P.calE T * (4 * π * D.Ncnt T))) := by gcongr; exact hs.trans hs2
      _ = 4 * π * C₁ * (P.calE T * (P.L T * D.Ncnt T)) := by ring
      _ ≤ 4 * π * C₁ * (P.calE T * ((2 * D.aT T) * P.L T * D.Ncnt T)) := by
          have h2a : (1:ℝ) ≤ 2 * D.aT T := by linarith
          have hnn : 0 ≤ P.calE T := hE0
          have hLN : 0 ≤ P.L T * D.Ncnt T := mul_nonneg hL0 hN0.le
          calc 4 * π * C₁ * (P.calE T * (P.L T * D.Ncnt T))
              = 4 * π * C₁ * (P.calE T * (1 * P.L T * D.Ncnt T)) := by ring
            _ ≤ 4 * π * C₁ * (P.calE T * (2 * D.aT T * P.L T * D.Ncnt T)) := by
                gcongr
          
      _ = 8 * π * C₁ * (P.calE T * (D.aT T * P.L T * D.Ncnt T)) := by ring
  exact le_trans h1 hB


/-- the D main term: (TL/2π)(b ℓ₁² + L² J) [eq:ratio-general]. -/
private def mainTr2D (P : Params) (q : ℕ) (D : DataDChi P) (T : ℝ) : ℝ :=
  T * P.L T / (2 * π) * (D.bT T * ell1q q T ^ 2 + P.L T ^ 2 * D.JT T)

/-- the D-form of [eq:tr2], first form (verbatim mirror of PrimeSide.tr2_first over FactsD). -/
private lemma tr2_firstD : EvBound
    (fun T => D.trG2 T - (2 * π * D.bT T * P.L T * D.intMu2 T + T / π * D.sumL2gq T))
    (fun T => P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := by
  have e3 : EvBound (fun T => D.Mmumu T - 2 * π * D.bT T * P.L T * D.intMu2 T)
      (fun T => P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := by
    refine h.prop_mumu.mono_right' one_pos ?_
    filter_upwards [regimeD h] with T ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩
    have hlogL : Real.log (P.L T) ≤ Real.log (l T) := Real.log_le_log (by linarith) hLl
    have hlogL0 : 0 ≤ Real.log (P.L T) := Real.log_nonneg hL
    calc l T ^ 2 * Real.log (P.L T) ≤ l T ^ 2 * Real.log (l T) := by gcongr
      _ = 1 * l T * Real.log (l T) * l T := by ring
      _ ≤ P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T) := by gcongr; nlinarith
      _ = 1 * (P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := (one_mul _).symm
  have e4 : EvBound (fun T => D.MPP T - T / π * D.sumL2gq T)
      (fun T => P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := by
    refine h.prop_PP.mono_right' one_pos ?_
    filter_upwards [regimeD h] with T ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩
    calc P.L T ^ 2 * P.X T = P.L T * P.L T * 1 * P.X T := by ring
      _ ≤ P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T) := by gcongr; nlinarith
      _ = 1 * (P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := (one_mul _).symm
  have hsqrtX : ∀ᶠ T in Filter.atTop, Real.sqrt (P.X T) ≤ P.X T := by
    filter_upwards [regimeD h] with T ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith
  have e5 : EvBound D.MmuP (fun T => P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := by
    refine h.cross_muP.mono_right' one_pos ?_
    filter_upwards [regimeD h, hsqrtX] with T ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩ hs
    calc l T * Real.sqrt (P.X T) ≤ l T * P.X T := by gcongr
      _ = 1 * l T * 1 * (0 + P.X T) := by ring
      _ ≤ P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T) := by gcongr; nlinarith
      _ = 1 * (P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)) := (one_mul _).symm
  have S := h.lem_ends.add (e3.add (e4.add (e5.const_mul 2)))
  refine S.congr_left ?_
  filter_upwards [h.Msplit] with T hM
  rw [hM]
  ring

/-- the D-form of [eq:tr2], second form: tr G̃² = (TL/2π)(bℓ₁² + L²J)(1 + O(𝓔_T)). -/
private lemma tr2D : EvBound (fun T => D.trG2 T - mainTr2D P q D T)
    (fun T => P.calE T * mainTr2D P q D T) := by
  have hlam := h.lam_pos
  have hw1 := h.one_le_w
  have hw : 0 ≤ P.w := by linarith
  obtain ⟨CR, hCR, hR⟩ := (tr2_firstD h).eventually_le
  obtain ⟨Cμ, hCμ, hμ⟩ := h.muints2.eventually_le
  obtain ⟨Cs, hCs, hsj⟩ := h.sumJ.eventually_le
  refine EvBound.of_eventually_le (c := 4 * π * CR + 2 * Cμ + 4 * Cs) (by positivity) ?_
  filter_upwards [hR, hμ, hsj, h.ab_range, regimeD h, PaperParams.calE_ge_w_div_L hlam hw,
    PaperParams.calE_ge_mid hlam hw, PaperParams.calE_nonneg_eventually hlam hw,
    PaperParams.eventually_L_ge P hlam (2 * P.w), Filter.eventually_gt_atTop (0:ℝ)]
    with T hR hμ hsj hab hreg hEw hEmid hE0 hL2w hT0
  obtain ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩ := hreg
  obtain ⟨hb2, hba, ha1, hJ0, -⟩ := hab
  have hSJ : |D.sumL2gq T - P.L T ^ 3 * D.JT T / 2| ≤ Cs * P.L T ^ 2 := by
    have e : P.L T ^ 3 * D.JT T / 2 = P.L T ^ 3 / 2 * D.JT T := by ring
    rw [e]
    exact hsj
  exact tr2D_pointwise T (P.L T) (ell1q q T) (l T) (P.X T) (P.calE T) (D.sumL2gq T) (D.intMu2 T)
    (D.bT T) (D.JT T) (D.trG2 T) P.w CR Cμ Cs hT hL hl hlog hX (ThmE.l_le_ell1q h.one_le_q hT0) hLl hw1 hL2w
    hb2 (hba.trans ha1) hJ0 hE0 hEw hEmid hCR.le hCμ.le hCs.le hR hμ hSJ

/-- the D-form of [eq:ratio]: (tr G̃)²/tr G̃² = cRatio(λ₁; a, b, J)·N·(1 + O(𝓔_T)). -/
private lemma ratioD : EvBound
    (fun T => D.trG T ^ 2 / D.trG2 T - cRatio (ThmE.lam1q P q T) (D.aT T) (D.bT T) (D.JT T) * D.Ncnt T)
    (fun T => P.calE T * (cRatio (ThmE.lam1q P q T) (D.aT T) (D.bT T) (D.JT T) * D.Ncnt T)) := by
  have hlam := h.lam_pos
  have hlam1 := h.lam_le_one
  have hw : 0 ≤ P.w := by linarith [h.one_le_w]
  obtain ⟨C₁, hC₁, h1⟩ := (tr1'D h).eventually_le
  obtain ⟨C₂, hC₂, h2⟩ := (tr2D h).eventually_le
  obtain ⟨A, hA, hN⟩ := h.rvm.eventually_le
  have hcal := PaperParams.calE_tendsto_zero hlam hlam1 hw
  have hs1 := ThmD.eventually_const_mul_le_half hcal hC₁
  have hs2 := ThmD.eventually_const_mul_le_half hcal hC₂
  refine EvBound.of_eventually_le (c := 2 * (2 * π * A + 5 * C₁ + C₂)) (by positivity) ?_
  filter_upwards [h1, h2, hN, hs1, hs2, regimeD h, h.ab_range, PaperParams.calE_ge_rpow hlam hw,
    PaperParams.calE_nonneg_eventually hlam hw, NcntD_pos h, Filter.eventually_ge_atTop (2 * π * A),
    Filter.eventually_gt_atTop (0:ℝ)]
    with T h1 h2 hN hs1 hs2 hreg hab hEr hE0 hN0 hTA hT0
  obtain ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩ := hreg
  obtain ⟨hb2, hba, -, hJ0, -⟩ := hab
  have hET : 1 / T ≤ P.calE T := by
    refine le_trans ?_ hEr
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  exact ratioD_pointwise T (P.L T) (ell1q q T) (l T) (P.calE T) (D.Ncnt T) (D.trG T) (D.trG2 T)
    A (D.aT T) (D.bT T) (D.JT T) C₁ C₂ hT (by linarith) (hl.trans (ThmE.l_le_ell1q h.one_le_q hT0)) (ThmE.l_le_ell1q h.one_le_q hT0)
    hN0 hE0 hET hA.le hC₁.le hC₂.le (le_trans hb2 hba) hb2 hJ0 hs1 hs2 hTA h1 h2 hN


end assemblyD

/-- the frhat field: the D-form hat-units second-moment upper bound. -/
private lemma frhatD {D : DataDChi P} (h : FactsDChi q D) : EvBound
    (fun T => max (D.trG2 T / (D.aT T * P.L T) ^ 2
        - (cRatio (ThmE.lam1q P q T) (D.aT T) (D.bT T) (D.JT T))⁻¹ * D.Ncnt T) 0)
    (fun T => P.calE T * ((cRatio (ThmE.lam1q P q T) (D.aT T) (D.bT T) (D.JT T))⁻¹ * D.Ncnt T)) := by
  have hlam := h.lam_pos
  have hw : 0 ≤ P.w := by linarith [h.one_le_w]
  obtain ⟨C₂, hC₂, h2⟩ := (tr2D h).eventually_le
  obtain ⟨A, hA, hN⟩ := h.rvm.eventually_le
  refine EvBound.of_eventually_le (c := 4 * π * A + 2 * C₂) (by positivity) ?_
  filter_upwards [h2, hN, regimeD h, h.ab_range, PaperParams.calE_ge_rpow hlam hw,
    PaperParams.calE_nonneg_eventually hlam hw, NcntD_pos h,
    Filter.eventually_ge_atTop (4 * π * A), Filter.eventually_gt_atTop (0:ℝ)]
    with T h2 hN hreg hab hEr hE0 hN0 hTA hT0
  obtain ⟨hT, hl, hlog, hL, hX, hLl, hXT⟩ := hreg
  obtain ⟨hb2, hba, -, hJ0, -⟩ := hab
  have hET : 1 / T ≤ P.calE T := by
    refine le_trans ?_ hEr
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  refine le_trans (le_of_eq (abs_of_nonneg (le_max_right _ _))) ?_
  exact frhatD_pointwise T (P.L T) (ell1q q T) (l T) (P.calE T) (D.Ncnt T) (D.trG2 T)
    A (D.aT T) (D.bT T) (D.JT T) C₂ hT (by linarith) (hl.trans (ThmE.l_le_ell1q h.one_le_q hT0))
    (ThmE.l_le_ell1q h.one_le_q hT0) hN0 hE0 hET hA.le hC₂.le (le_trans hb2 hba) hb2 hJ0 hTA h2 hN

/-- **[eq:ratio-general] for L(s,χ), assembled.** -/
theorem tracesBoundsDChi_of_factsDChi (h : FactsDChi q D) :
    TracesBoundsDChi P q D.aT D.bT D.JT D.trG D.trG2 D.Ncnt where
  tr1 := h.prop_trace
  ratio := ratioD h
  frhat := frhatD h

end ThmDE
end Zeta23

end
