/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmE/LandauChi.lean — Landau partial fraction for L'/L(s,χ) (χ nontrivial):
transplant of Zeta23/WeilEF/Landau.lean's zeta_logDeriv_partial_fraction via the f-generic
Zeta23.WeilEF.logDeriv_partial_fraction_disk.  Simpler than the ζ-case: L(·,χ) is entire
(no pole exclusion) and the growth bound (LGrowth.LFunction_growth_right_uniform) is uniform
over the whole disk and fully explicit (8q(|Im|+3)); the center lower bound is
LGrowth.LFunction_lower_bound_two (1/3).
-/
import Zeta23.WeilEF.Landau
import Zeta23.ThmE.LGrowth

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Complex MeasureTheory Real Set
open scoped BigOperators

namespace Zeta23
namespace ThmE

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

set_option maxHeartbeats 800000 in
/-- **Partial fraction for L'/L(s,χ) at height t** (|t| ≥ 6, χ ≠ 1): a finite set Z — the
L-zeros within distance (22/25)·(91/50) of 2+it — with Σ-multiplicity ≤ C·log(q(|t|+3)) and
L'/L(s) = Σ_{ρ ∈ Z} m_ρ/(s−ρ) + O(log(q(|t|+3))) on the ball of radius 3/2 around 2+it. -/
theorem L_logDeriv_partial_fraction (hχ1 : χ ≠ 1) : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 6 ≤ |t| →
    ∃ Z : Finset ℂ,
      ((Z : Set ℂ) = {ρ ∈ Metric.closedBall (2 + t * I) (22/25 * (91/50)) | χ.LFunction ρ = 0}) ∧
      ((∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℝ))
        ≤ C * Real.log ((q : ℝ) * (|t| + 3))) ∧
      ∀ s ∈ Metric.closedBall (2 + t * I) (3/2), χ.LFunction s ≠ 0 →
        ‖logDeriv χ.LFunction s - ∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℂ) / (s - ρ)‖
          ≤ C * Real.log ((q : ℝ) * (|t| + 3)) := by
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast NeZero.pos q
  refine ⟨(44795000 * 50 / 91) * (Real.log 72 + 3) + 12 * (Real.log 72 + 3), by positivity,
    fun t ht => ?_⟩
  set s₀ : ℂ := 2 + t * I with hs₀
  have hs₀re : s₀.re = 2 := by simp [hs₀]
  have hLs₀ : χ.LFunction s₀ ≠ 0 :=
    LFunction_ne_zero_of_two_le_re (by rw [hs₀re])
  have hlow : (1/3 : ℝ) ≤ ‖χ.LFunction s₀‖ := LFunction_lower_bound_two (by rw [hs₀re])
  have hfa : AnalyticOnNhd ℂ χ.LFunction (Metric.closedBall s₀ (91/50)) := fun s _ =>
    (DirichletCharacter.differentiable_LFunction hχ1).analyticAt s
  set B : ℝ := 24 * (q : ℝ) * (|t| + 5) with hB
  have hB2 : 2 ≤ B := by
    rw [hB]
    nlinarith [abs_nonneg t]
  have hfB : ∀ w ∈ Metric.closedBall s₀ (24/25 * (91/50)),
      ‖χ.LFunction w‖ ≤ B * ‖χ.LFunction s₀‖ := by
    intro w hw
    rw [Metric.mem_closedBall, Complex.dist_eq] at hw
    have hwre : (0.15 : ℝ) ≤ w.re := by
      have h := Complex.abs_re_le_norm (w - s₀)
      have hre : (w - s₀).re = w.re - 2 := by simp [hs₀]
      rw [hre] at h
      have := abs_le.mp (h.trans hw)
      linarith [this.1]
    have hwim : |w.im| ≤ |t| + 2 := by
      have h := Complex.abs_im_le_norm (w - s₀)
      have him : (w - s₀).im = w.im - t := by simp [hs₀]
      rw [him] at h
      have h4 : |w.im - t| ≤ 24/25 * (91/50) := h.trans hw
      have h3 : |w.im| - |t| ≤ |w.im - t| := abs_sub_abs_le_abs_sub w.im t
      linarith
    calc ‖χ.LFunction w‖ ≤ 8 * q * (|w.im| + 3) := LFunction_growth_right_uniform hχ1 hwre
      _ ≤ 8 * q * (|t| + 5) := by
          have h8q : (0:ℝ) ≤ 8 * (q:ℝ) := by positivity
          nlinarith [mul_le_mul_of_nonneg_left (show |w.im| + 3 ≤ |t| + 5 by linarith) h8q]
      _ = B * (1/3) := by rw [hB]; ring
      _ ≤ B * ‖χ.LFunction s₀‖ := by
          refine mul_le_mul_of_nonneg_left hlow ?_
          rw [hB]
          positivity
  obtain ⟨Z, hZset, hZcount, hZpf⟩ := Zeta23.WeilEF.logDeriv_partial_fraction_disk
    (f := χ.LFunction) (by norm_num : (0:ℝ) < 91/50) hfa hLs₀ hB2 hfB
  have hlogB : Real.log B ≤ (Real.log 72 + 3) * Real.log ((q:ℝ) * (|t| + 3)) := by
    have hqt3 : (1:ℝ) < (q:ℝ) * (|t| + 3) := by nlinarith [abs_nonneg t]
    have hlog1 : (2:ℝ) ≤ Real.log ((q:ℝ) * (|t| + 3)) := by
      rw [Real.le_log_iff_exp_le (by nlinarith [abs_nonneg t])]
      have h1 := Real.exp_one_lt_d9
      calc Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
        _ ≤ 2.7182818286 * 2.7182818286 := by nlinarith [Real.exp_pos 1]
        _ ≤ 9 := by norm_num
        _ ≤ (q:ℝ) * (|t| + 3) := by nlinarith
    have h1 : B ≤ 72 * ((q:ℝ) * (|t| + 3)) := by
      rw [hB]
      nlinarith [abs_nonneg t]
    have h2 : Real.log B ≤ Real.log 72 + Real.log ((q:ℝ) * (|t| + 3)) := by
      calc Real.log B ≤ Real.log (72 * ((q:ℝ) * (|t| + 3))) :=
            Real.log_le_log (by rw [hB]; positivity) h1
        _ = Real.log 72 + Real.log ((q:ℝ) * (|t| + 3)) :=
            Real.log_mul (by norm_num) (by positivity)
    have h72 : (0:ℝ) ≤ Real.log 72 := Real.log_nonneg (by norm_num)
    nlinarith [mul_nonneg h72 (by linarith : (0:ℝ) ≤ Real.log ((q:ℝ) * (|t| + 3)) - 1)]
  have hlogpos : (0:ℝ) < Real.log ((q:ℝ) * (|t| + 3)) := by
    have : (1:ℝ) < (q:ℝ) * (|t| + 3) := by nlinarith [abs_nonneg t]
    exact Real.log_pos this
  refine ⟨Z, hZset, ?_, ?_⟩
  · refine hZcount.trans ?_
    have hlog1211 : (1:ℝ)/12 ≤ Real.log ((24/25 : ℝ)/(22/25)) := by
      rw [show ((24/25 : ℝ))/(22/25) = 12/11 by norm_num]
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 11/12 by norm_num)
      rw [show (11/12:ℝ) = (12/11)⁻¹ by norm_num, Real.log_inv] at h
      linarith
    have hlp : (0:ℝ) < Real.log ((24/25 : ℝ)/(22/25)) := by
      rw [show ((24/25 : ℝ))/(22/25) = 12/11 by norm_num]
      exact Real.log_pos (by norm_num)
    have hlogBnn : (0:ℝ) ≤ Real.log B := Real.log_nonneg (by linarith)
    calc 1 / Real.log ((24/25 : ℝ)/(22/25)) * Real.log B ≤ 12 * Real.log B := by
          refine mul_le_mul_of_nonneg_right ?_ hlogBnn
          rw [div_le_iff₀ hlp]
          linarith
      _ ≤ 12 * ((Real.log 72 + 3) * Real.log ((q:ℝ) * (|t| + 3))) :=
          mul_le_mul_of_nonneg_left hlogB (by norm_num)
      _ ≤ ((44795000 * 50 / 91) * (Real.log 72 + 3) + 12 * (Real.log 72 + 3))
            * Real.log ((q:ℝ) * (|t| + 3)) := by
          have h72 : (0:ℝ) ≤ Real.log 72 := Real.log_nonneg (by norm_num)
          nlinarith
  · intro s hs hLs
    have hs' : s ∈ Metric.closedBall s₀ (83/100 * (91/50)) :=
      Metric.closedBall_subset_closedBall (by norm_num) hs
    refine (hZpf s hs' hLs).trans ?_
    calc 44795000 / (91/50) * Real.log B
        ≤ 44795000 / (91/50) * ((Real.log 72 + 3) * Real.log ((q:ℝ) * (|t| + 3))) :=
          mul_le_mul_of_nonneg_left hlogB (by norm_num)
      _ ≤ ((44795000 * 50 / 91) * (Real.log 72 + 3) + 12 * (Real.log 72 + 3))
            * Real.log ((q:ℝ) * (|t| + 3)) := by
          have h72 : (0:ℝ) ≤ Real.log 72 := Real.log_nonneg (by norm_num)
          nlinarith

end ThmE
end Zeta23
