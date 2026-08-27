/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/ExplicitFormula/LineBound.lean — bounds and continuity for E = ξ′/ξ and ξ″/ξ′ on the line Re s = 5/4
(consumed by the contour `hline` hypothesis and the EF integrability).

  norm_Efn_line                    : ‖E(5/4+it)‖ ≤ C log(2+|t|)
  norm_logDeriv_xiDeriv_line (hF2) : ‖ξ″/ξ′(5/4+it)‖ ≤ C log(2+|t|)
  continuous_Efn_line, continuous_logDeriv_xiDeriv_line (hF2).
Route: E = L + ζ′/ζ with ‖L(5/4+it)‖ ≤ ‖Γℝ′/Γℝ‖ + ‖1/s‖ + ‖1/(s−1)‖ ≤ C_Γ log(2+|t|) + 4/5 + 4
(Zeta23.WeilEF.norm_logDeriv_Gammaℝ_le) and ‖ζ′/ζ‖ = ‖A‖ ≤ A₀ (Expansion.norm_Afn_le); then ξ″/ξ′ = E + E′/E
(Expansion.logDeriv_xiDeriv_eq_Efn) with ‖E′/E‖ ≤ CE (Expansion.derivE_div_E_uniform); log(2+|t|) ≥ log 2
absorbs the constants.
-/
import Zeta23.XiPrime.ExplicitFormula.Expansion

open Complex Set Filter Topology

noncomputable section

namespace Zeta23
namespace XiPrime

private lemma log_two_add_abs_ge (t : ℝ) : Real.log 2 ≤ Real.log (2 + |t|) :=
  Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])

private lemma half_le_log_two_add_abs (t : ℝ) : (1 : ℝ) / 2 ≤ Real.log (2 + |t|) :=
  le_trans (by have := Real.log_two_gt_d9; linarith) (log_two_add_abs_ge t)

/-- ‖L(5/4 + it)‖ ≤ C log(2 + |t|). -/
theorem norm_Lfn_line : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
    ‖Lfn (((5 / 4 : ℝ) : ℂ) + t * I)‖ ≤ C * Real.log (2 + |t|) := by
  obtain ⟨CΓ, hCΓ, hΓ⟩ := Zeta23.WeilEF.norm_logDeriv_Gammaℝ_le
  refine ⟨CΓ + 10, by positivity, fun t => ?_⟩
  set s : ℂ := ((5 / 4 : ℝ) : ℂ) + t * I with hs
  have hG := hΓ (5 / 4) t (by norm_num) (by norm_num)
  have h1 : ‖1 / s‖ ≤ 4 / 5 := by
    rw [norm_div, norm_one]
    have : (5 / 4 : ℝ) ≤ ‖s‖ := by
      have := Complex.abs_re_le_norm s
      rw [hs, re_54] at this
      rw [abs_of_pos (by norm_num)] at this
      exact this
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have h2 : ‖1 / (s - 1)‖ ≤ 4 := by
    rw [norm_div, norm_one]
    have : (1 / 4 : ℝ) ≤ ‖s - 1‖ := by
      have := Complex.abs_re_le_norm (s - 1)
      have hre : (s - 1).re = 1 / 4 := by rw [Complex.sub_re, hs, re_54]; norm_num
      rw [hre, abs_of_pos (by norm_num)] at this
      exact this
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hL := half_le_log_two_add_abs t
  calc ‖Lfn s‖ = ‖logDeriv Complex.Gammaℝ s + 1 / s + 1 / (s - 1)‖ := rfl
    _ ≤ ‖logDeriv Complex.Gammaℝ s‖ + ‖1 / s‖ + ‖1 / (s - 1)‖ := norm_add₃_le
    _ ≤ CΓ * Real.log (2 + |t|) + 4 / 5 + 4 := by rw [hs]; linarith [hG, h1, h2]
    _ ≤ (CΓ + 10) * Real.log (2 + |t|) := by nlinarith

/-- **‖E(5/4 + it)‖ ≤ C log(2 + |t|)**, E = ξ′/ξ = L + ζ′/ζ. -/
theorem norm_Efn_line : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
    ‖Efn (((5 / 4 : ℝ) : ℂ) + t * I)‖ ≤ C * Real.log (2 + |t|) := by
  obtain ⟨CL, hCL, hL⟩ := norm_Lfn_line
  obtain ⟨A₀, hA0, hA⟩ := norm_Afn_le
  refine ⟨CL + 2 * A₀ + 1, by positivity, fun t => ?_⟩
  have hlog := half_le_log_two_add_abs t
  have h : ‖logDeriv riemannZeta (((5 / 4 : ℝ) : ℂ) + t * I)‖ ≤ A₀ := by
    rw [logDeriv_zeta_eq_neg_Afn (one_lt_re_54 t), norm_neg]; exact hA t
  calc ‖Efn (((5 / 4 : ℝ) : ℂ) + t * I)‖
      ≤ ‖Lfn (((5 / 4 : ℝ) : ℂ) + t * I)‖ + ‖logDeriv riemannZeta (((5 / 4 : ℝ) : ℂ) + t * I)‖ :=
        norm_add_le _ _
    _ ≤ CL * Real.log (2 + |t|) + A₀ := add_le_add (hL t) h
    _ ≤ (CL + 2 * A₀ + 1) * Real.log (2 + |t|) := by nlinarith

/-- **‖ξ″/ξ′(5/4 + it)‖ ≤ C log(2 + |t|)** under (F2) (ξ′ ≠ 0 on the line). -/
theorem norm_logDeriv_xiDeriv_line (hF2 : XiDerivZerosInStrip) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      ‖logDeriv xiDeriv (((5 / 4 : ℝ) : ℂ) + t * I)‖ ≤ C * Real.log (2 + |t|) := by
  obtain ⟨CEn, hCEn, hEn⟩ := norm_Efn_line
  obtain ⟨CE, hCE0, hCE⟩ := derivE_div_E_uniform hF2
  refine ⟨CEn + 2 * CE + 1, by positivity, fun t => ?_⟩
  have hlog := half_le_log_two_add_abs t
  rw [logDeriv_xiDeriv_eq_Efn (one_lt_re_54 t) (xiDeriv_ne_zero_line hF2 t)]
  calc ‖Efn (((5 / 4 : ℝ) : ℂ) + t * I)
        + deriv Efn (((5 / 4 : ℝ) : ℂ) + t * I) / Efn (((5 / 4 : ℝ) : ℂ) + t * I)‖
      ≤ ‖Efn (((5 / 4 : ℝ) : ℂ) + t * I)‖
        + ‖deriv Efn (((5 / 4 : ℝ) : ℂ) + t * I) / Efn (((5 / 4 : ℝ) : ℂ) + t * I)‖ := norm_add_le _ _
    _ ≤ CEn * Real.log (2 + |t|) + CE := add_le_add (hEn t) (hCE t)
    _ ≤ (CEn + 2 * CE + 1) * Real.log (2 + |t|) := by nlinarith

/-- E is continuous along the line Re s = 5/4. -/
theorem continuous_Efn_line : Continuous (fun t : ℝ => Efn (((5 / 4 : ℝ) : ℂ) + t * I)) := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  exact ((analyticAt_Efn (one_lt_re_54 t)).continuousAt).comp
    (f := fun t : ℝ => ((5 / 4 : ℝ) : ℂ) + t * I) (x := t) (by fun_prop)

/-- ξ″/ξ′ is continuous along the line Re s = 5/4 (ξ′ entire and zero-free there under (F2)). -/
theorem continuous_logDeriv_xiDeriv_line (hF2 : XiDerivZerosInStrip) :
    Continuous (fun t : ℝ => logDeriv xiDeriv (((5 / 4 : ℝ) : ℂ) + t * I)) := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hne := xiDeriv_ne_zero_line hF2 t
  have ha := xiDeriv_analyticAt (((5 / 4 : ℝ) : ℂ) + t * I)
  have hc : ContinuousAt (logDeriv xiDeriv) (((5 / 4 : ℝ) : ℂ) + t * I) := by
    have := (ha.deriv.continuousAt).div ha.continuousAt hne
    simpa only [logDeriv] using this
  exact hc.comp (f := fun t : ℝ => ((5 / 4 : ℝ) : ℂ) + t * I) (x := t) (by fun_prop)

end XiPrime
end Zeta23
