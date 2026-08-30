/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/Landau.lean

Landau's lemma (Borel–Carathéodory + Jensen route; Mathlib: Analysis/Complex/BorelCaratheodory,
JensenFormula): zero counts and the partial-fraction expansion of f'/f on disks, specialized to ζ.
`zeta_local_zero_count` is consumed downstream as `RiemannVonMangoldt.local_count`.
-/
import Zeta23.RvM.ZetaGrowth
import Zeta23.FromPNTPlus.StrongPNTPrefix
import Zeta23.Statement

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex Set


section UnitDisk

open Metric

/-- Cf never vanishes on the closed ball over which the zeros were divided out. -/
lemma Cf_ne_zero {f : ℂ → ℂ} (hfa : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf0 : f 0 ≠ 0) {r : ℝ} (hr1 : r < 1) (hfin : (SetOfZeros 1 f).Finite)
    {z : ℂ} (hz : ‖z‖ ≤ r) : Cf r f z ≠ 0 := by
  have hfinr := finiteSetOfZeros_mono hr1 hfin
  by_cases hmem : z ∈ SetOfZeros r f
  · -- regularized value: ZeroFactor f z ≠ 0 over a nonvanishing finite product
    obtain ⟨h_ρ, _, hρ0, hZF, _⟩ := ZeroFactorization hr1 hfa hf0 hmem
    unfold Cf
    rw [dif_pos hfinr, dif_pos hmem, hZF]
    apply div_ne_zero hρ0
    refine Finset.prod_ne_zero_iff.mpr fun ρ hρ => ?_
    have hne : z ≠ ρ := by
      intro h
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hρ
      exact hρ.2 h.symm
    exact pow_ne_zero _ (sub_ne_zero.mpr hne)
  · unfold Cf
    rw [dif_pos hfinr, dif_neg hmem]
    have hfz : f z ≠ 0 := by
      intro h
      exact hmem ⟨hz, h⟩
    apply div_ne_zero hfz
    refine Finset.prod_ne_zero_iff.mpr fun ρ hρ => ?_
    have hρ' := hfinr.mem_toFinset.mp hρ
    have hne : z ≠ ρ := by
      rintro rfl
      exact hmem hρ'
    exact pow_ne_zero _ (sub_ne_zero.mpr hne)

/-- Away from the zero set, `f = Π (z−ρ)^{m_ρ} · Cf`. -/
lemma f_eq_prod_mul_Cf {f : ℂ → ℂ} {r : ℝ} (hr1 : r < 1) (hfin : (SetOfZeros 1 f).Finite)
    {z : ℂ} (hz : z ∉ SetOfZeros r f) :
    f z = (∏ ρ ∈ (finiteSetOfZeros_mono hr1 hfin).toFinset, (z - ρ) ^ analyticOrderNatAt f ρ)
      * Cf r f z := by
  have hfinr := finiteSetOfZeros_mono hr1 hfin
  unfold Cf
  rw [dif_pos hfinr, dif_neg hz]
  rw [mul_div_cancel₀]
  refine Finset.prod_ne_zero_iff.mpr fun ρ hρ => ?_
  have hρ' := hfinr.mem_toFinset.mp hρ
  have hne : z ≠ ρ := by
    rintro rfl
    exact hz hρ'
  exact pow_ne_zero _ (sub_ne_zero.mpr hne)

/-- logDeriv of the finite zero product: `logDeriv (Π (·−ρ)^{m_ρ}) z = Σ m_ρ/(z−ρ)`
(Mathlib's `logDeriv_prod` + `logDeriv_fun_pow`). -/
lemma logDeriv_zero_prod {s : Finset ℂ} {m : ℂ → ℕ} {z : ℂ} (hz : ∀ ρ ∈ s, z ≠ ρ) :
    logDeriv (fun w => ∏ ρ ∈ s, (w - ρ) ^ m ρ) z = ∑ ρ ∈ s, (m ρ : ℂ) / (z - ρ) := by
  rw [logDeriv_prod (f := fun ρ w => (w - ρ) ^ m ρ)
    (fun ρ hρ => pow_ne_zero _ (sub_ne_zero.mpr (hz ρ hρ))) (fun ρ _ => by fun_prop)]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have hd : HasDerivAt (fun w : ℂ => w - ρ) 1 z := (hasDerivAt_id z).sub_const ρ
  rw [logDeriv_fun_pow hd.differentiableAt, logDeriv_apply, hd.deriv]
  ring

/-- logDeriv splits into the zero sum plus the regular part, at non-zeros inside the divided
ball. -/
lemma logDeriv_split {f : ℂ → ℂ} (hfa : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1))
    (hf0 : f 0 ≠ 0) {r : ℝ} (hr1 : r < 1) (hfin : (SetOfZeros 1 f).Finite)
    {z : ℂ} (hz : ‖z‖ < r) (hfz : f z ≠ 0) :
    logDeriv f z = (∑ ρ ∈ (finiteSetOfZeros_mono hr1 hfin).toFinset,
        (analyticOrderNatAt f ρ : ℂ) / (z - ρ)) + logDeriv (Cf r f) z := by
  have hfinr := finiteSetOfZeros_mono hr1 hfin
  set P0 : ℂ → ℂ := fun w => ∏ ρ ∈ hfinr.toFinset, (w - ρ) ^ analyticOrderNatAt f ρ with hP0
  have hU : IsOpen (Metric.ball (0 : ℂ) r \ SetOfZeros r f) :=
    Metric.isOpen_ball.sdiff hfinr.isClosed
  have hzU : z ∈ Metric.ball (0 : ℂ) r \ SetOfZeros r f :=
    ⟨mem_ball_zero_iff.mpr hz, fun h => hfz h.2⟩
  have heq : f =ᶠ[nhds z] fun w => P0 w * Cf r f w := by
    filter_upwards [hU.mem_nhds hzU] with w hw
    exact f_eq_prod_mul_Cf hr1 hfin hw.2
  have hzne : ∀ ρ ∈ hfinr.toFinset, z ≠ ρ := by
    intro ρ hρ
    rintro rfl
    exact hfz (hfinr.mem_toFinset.mp hρ).2
  have hP0z : P0 z ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (sub_ne_zero.mpr (hzne ρ hρ))
  have hCfz : Cf r f z ≠ 0 := Cf_ne_zero hfa hf0 hr1 hfin hz.le
  have hdP0 : DifferentiableAt ℂ P0 z :=
    DifferentiableAt.fun_finsetProd fun ρ _ =>
      ((differentiable_id.sub_const ρ).differentiableAt).pow _
  have hdCf : DifferentiableAt ℂ (Cf r f) z := by
    have hR : r < (r + 1) / 2 := by linarith
    have hR1 : (r + 1) / 2 < 1 := by linarith
    exact ((CfAnalytic hR hR1 hfa hf0) z (by
      rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero]
      calc ‖z‖ ≤ r := hz.le
        _ ≤ (r + 1) / 2 := by linarith)).differentiableAt
  calc logDeriv f z = logDeriv (fun w => P0 w * Cf r f w) z := by
        unfold logDeriv
        simp only [Pi.div_apply]
        rw [heq.deriv_eq, heq.eq_of_nhds]
    _ = logDeriv P0 z + logDeriv (Cf r f) z := logDeriv_mul z hP0z hCfz hdP0 hdCf
    _ = _ := by rw [hP0, logDeriv_zero_prod hzne]

/-- Borel–Carathéodory bound for the regular part: with zeros divided over ‖ρ‖ ≤ 22/25 and
‖f‖ ≤ B on ‖z‖ ≤ 24/25 (f(0) = 1, 2 ≤ B), `‖logDeriv (Cf (22/25) f) z‖ ≤ 44795000 log B` on
‖z‖ ≤ 83/100. -/
lemma norm_logDeriv_Cf_le {f : ℂ → ℂ} {B : ℝ}
    (hfa : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) (hf0 : f 0 = 1)
    (hfin : (SetOfZeros 1 f).Finite) (hB2 : 2 ≤ B)
    (hfB : ∀ w : ℂ, ‖w‖ ≤ 24/25 → ‖f w‖ ≤ B)
    {z : ℂ} (hz : ‖z‖ ≤ 83/100) :
    ‖logDeriv (Cf (22/25) f) z‖ ≤ 44795000 * Real.log B := by
  have hf0' : f 0 ≠ 0 := by rw [hf0]; exact one_ne_zero
  have hfinr : (SetOfZeros (22/25) f).Finite := finiteSetOfZeros_mono (by norm_num) hfin
  have hlogB : 0 < Real.log B := Real.log_pos (by linarith)
  -- total multiplicity bound (ZerosBound with r = 22/25, R = 24/25)
  have hcount : ((∑ ρ ∈ (finiteSetOfZeros_mono (by norm_num : (22/25 : ℝ) < 1) hfin).toFinset,
      analyticOrderNatAt f ρ : ℕ) : ℝ) ≤ 1 / Real.log ((24/25) / (22/25)) * Real.log B := by
    exact_mod_cast ZerosBound (by norm_num) (by norm_num)
      (by norm_num : (22/25:ℝ) < 24/25) (by norm_num) hfa hf0 hfin (fun w hw => hfB w hw)
  set K : ℕ := ∑ ρ ∈ (finiteSetOfZeros_mono (by norm_num : (22/25 : ℝ) < 1) hfin).toFinset,
    analyticOrderNatAt f ρ with hK
  -- Cf on the sphere of radius 24/25
  have hsphere : ∀ w : ℂ, ‖w‖ = 24/25 → ‖Cf (22/25) f w‖ ≤ B * (25/2 : ℝ) ^ K := by
    intro w hw
    have hwmem : w ∉ SetOfZeros (22/25) f := by
      intro h
      have := h.1
      rw [hw] at this
      norm_num at this
    have hfinr34 := finiteSetOfZeros_mono (by norm_num : (22/25 : ℝ) < 1) hfin
    have hdist : ∀ ρ ∈ hfinr34.toFinset, (2/25 : ℝ) ≤ ‖w - ρ‖ := by
      intro ρ hρ
      have hρ' := hfinr34.mem_toFinset.mp hρ
      calc (2/25 : ℝ) = 24/25 - 22/25 := by norm_num
        _ ≤ ‖w‖ - ‖ρ‖ := by
            have := hρ'.1
            rw [hw]
            linarith
        _ ≤ ‖w - ρ‖ := norm_sub_norm_le w ρ
    have hprod_lb : ((2/25 : ℝ)) ^ K ≤ ‖∏ ρ ∈ hfinr34.toFinset, (w - ρ) ^ analyticOrderNatAt f ρ‖ := by
      rw [norm_prod, hK, ← Finset.prod_pow_eq_pow_sum]
      refine Finset.prod_le_prod (fun ρ _ => by positivity) (fun ρ hρ => ?_)
      rw [norm_pow]
      exact pow_le_pow_left₀ (by norm_num) (hdist ρ hρ) _
    unfold Cf
    rw [dif_pos hfinr34, dif_neg hwmem]
    rw [norm_div]
    have hprod_pos : (0:ℝ) < ‖∏ ρ ∈ hfinr34.toFinset, (w - ρ) ^ analyticOrderNatAt f ρ‖ :=
      lt_of_lt_of_le (by positivity) hprod_lb
    rw [div_le_iff₀ hprod_pos]
    calc ‖f w‖ ≤ B := hfB w (le_of_eq hw)
      _ = B * (25/2 : ℝ) ^ K * (2/25 : ℝ) ^ K := by
          rw [mul_assoc, ← mul_pow]
          norm_num
      _ ≤ B * (25/2 : ℝ) ^ K * ‖∏ ρ ∈ hfinr34.toFinset, (w - ρ) ^ analyticOrderNatAt f ρ‖ := by
          have hB0 : (0:ℝ) ≤ B * (25/2 : ℝ) ^ K := by positivity
          exact mul_le_mul_of_nonneg_left hprod_lb hB0
  -- inside by the maximum principle
  have hball : ∀ w : ℂ, ‖w‖ ≤ 24/25 → ‖Cf (22/25) f w‖ ≤ B * (25/2 : ℝ) ^ K := by
    intro w hw
    have hCfa : AnalyticOn ℂ (Cf (22/25) f) (Metric.closedBall 0 (24/25)) :=
      ((CfAnalytic (by norm_num : (22/25:ℝ) < 39/40) (by norm_num) hfa hf0').mono
        (Metric.closedBall_subset_closedBall (by norm_num))).analyticOn
    refine AnalyticOn.norm_le_of_norm_le_on_sphere le_rfl hCfa (fun v hv => ?_)
      (by rwa [Metric.mem_closedBall, Complex.dist_eq, sub_zero])
    refine hsphere v ?_
    rw [mem_sphere_iff_norm, sub_zero] at hv
    exact hv
  -- lower bound at the centre
  have hCf0 : (1:ℝ) ≤ ‖Cf (22/25) f 0‖ := by
    have h0mem : (0:ℂ) ∉ SetOfZeros (22/25) f := fun h => hf0' h.2
    have hfinr34 := finiteSetOfZeros_mono (by norm_num : (22/25 : ℝ) < 1) hfin
    unfold Cf
    rw [dif_pos hfinr34, dif_neg h0mem, norm_div, hf0, norm_one]
    rw [le_div_iff₀]
    · rw [one_mul, norm_prod]
      refine Finset.prod_le_one (fun ρ _ => by positivity) (fun ρ hρ => ?_)
      have hρ' := hfinr34.mem_toFinset.mp hρ
      rw [norm_pow]
      refine pow_le_one₀ (norm_nonneg _) ?_
      rw [zero_sub, norm_neg]
      linarith [hρ'.1]
    · rw [norm_prod]
      refine Finset.prod_pos (fun ρ hρ => ?_)
      have hρ' := hfinr34.mem_toFinset.mp hρ
      have hρ0 : ρ ≠ 0 := by
        rintro rfl
        exact hf0' hρ'.2
      rw [norm_pow, zero_sub, norm_neg]
      exact pow_pos (norm_pos_iff.mpr hρ0) _
  -- the analytic logarithm and Borel–Carathéodory
  obtain ⟨J, hJa, hJ0, hJd, hJre⟩ := LogOfAnalyticFunction
    (by norm_num : (0:ℝ) < 17/20) (by norm_num : (17/20:ℝ) < 22/25)
    ((CfAnalytic (by norm_num : (22/25:ℝ) < 9/10) (by norm_num) hfa hf0').mono
      (Metric.closedBall_subset_closedBall (by norm_num)))
    (fun v hv => Cf_ne_zero hfa hf0' (by norm_num) hfin
      (by rwa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] at hv))
  set M' : ℝ := (1 + Real.log (25/2) / Real.log ((24/25) / (22/25))) * Real.log B with hM'
  have hlog76 : (0:ℝ) < Real.log ((24/25) / (22/25)) := Real.log_pos (by norm_num)
  have hM'pos : 0 < M' := by
    rw [hM']
    have : (0:ℝ) < 1 + Real.log (25/2) / Real.log ((24/25) / (22/25)) := by positivity
    positivity
  have hre : ∀ v ∈ Metric.closedBall (0:ℂ) (17/20), (J v).re ≤ M' := by
    intro v hv
    rw [← (hJre v (Metric.closedBall_subset_ball (by norm_num) hv))]
    have hv' : ‖v‖ ≤ 24/25 := by
      rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero] at hv
      linarith
    have h1 : Real.log ‖Cf (22/25) f v‖ ≤ Real.log (B * (25/2 : ℝ) ^ K) := by
      rcases eq_or_ne (Cf (22/25) f v) 0 with h | h
      · rw [h, norm_zero, Real.log_zero]
        refine Real.log_nonneg ?_
        calc (1:ℝ) = 1 * 1 := by ring
          _ ≤ B * (25/2 : ℝ) ^ K := by
              refine mul_le_mul (by linarith) (one_le_pow₀ (by norm_num)) (by norm_num)
                (by linarith)
      · exact Real.log_le_log (norm_pos_iff.mpr h) (hball v hv')
    have h2 : (0:ℝ) ≤ Real.log ‖Cf (22/25) f 0‖ := Real.log_nonneg hCf0
    have h3 : Real.log (B * (25/2 : ℝ) ^ K) = Real.log B + K * Real.log (25/2) := by
      rw [Real.log_mul (by linarith) (by positivity), Real.log_pow]
    have h4 : (K : ℝ) * Real.log (25/2) ≤ (Real.log B / Real.log ((24/25)/(22/25))) * Real.log (25/2) := by
      have hlog8 : (0:ℝ) ≤ Real.log (25/2) := Real.log_nonneg (by norm_num)
      have hKle : (K:ℝ) ≤ Real.log B / Real.log ((24/25)/(22/25)) := by
        rw [div_eq_inv_mul, ← one_div]
        exact hcount
      exact mul_le_mul_of_nonneg_right hKle hlog8
    have h5 : Real.log ‖Cf (22/25) f v‖ - Real.log ‖Cf (22/25) f 0‖
        ≤ Real.log B + (K:ℝ) * Real.log (25/2) := by
      rw [← h3]
      linarith
    rw [hM']
    calc Real.log ‖Cf (22/25) f v‖ - Real.log ‖Cf (22/25) f 0‖
        ≤ Real.log B + (K:ℝ) * Real.log (25/2) := h5
      _ ≤ Real.log B + (Real.log B / Real.log ((24/25)/(22/25))) * Real.log (25/2) := by linarith
      _ = (1 + Real.log (25/2) / Real.log ((24/25) / (22/25))) * Real.log B := by
          field_simp
  have hbc := BorelCaratheodoryDeriv hM'pos (by norm_num : (0:ℝ) < 83/100)
    (by norm_num : (83/100:ℝ) < 17/20)
    ((hJa.mono (Metric.ball_subset_ball (by norm_num))).analyticOn) hJ0
    (fun v hv => hre v (Metric.ball_subset_closedBall hv))
    (by rwa [Metric.mem_closedBall, Complex.dist_eq, sub_zero])
  have hzmem : z ∈ Metric.closedBall (0:ℂ) (17/20) := by
    rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero]
    linarith
  have hderivJ : deriv J z = logDeriv (Cf (22/25) f) z := by
    rw [hJd z (by
      rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero]
      linarith), logDeriv]
    rfl
  rw [← hderivJ]
  refine hbc.trans ?_
  -- 16 * M' * (17/20)^2 / (17/20 - 83/100)^3 = 1445000 * M' ≤ 1445000 * 31 * log B
  have hM'le : M' ≤ 31 * Real.log B := by
    rw [hM']
    have h8 : Real.log (25/2) ≤ 30 * Real.log ((24/25) / (22/25)) := by
      have h714 : (25/2:ℝ) ≤ ((24/25)/(22/25)) ^ (30:ℕ) := by norm_num
      calc Real.log (25/2) ≤ Real.log (((24/25)/(22/25)) ^ (30:ℕ)) :=
            Real.log_le_log (by norm_num) h714
        _ = 30 * Real.log ((24/25)/(22/25)) := by rw [Real.log_pow]; push_cast; ring
    have hcoef : 1 + Real.log (25/2) / Real.log ((24/25) / (22/25)) ≤ 31 := by
      have hd : Real.log (25/2) / Real.log ((24/25)/(22/25)) ≤ 30 :=
        (div_le_iff₀ hlog76).mpr (by linarith)
      linarith
    exact mul_le_mul_of_nonneg_right hcoef hlogB.le
  calc 16 * M' * (17/20:ℝ) ^ 2 / ((17/20:ℝ) - 83/100) ^ 3 = 1445000 * M' := by
        field_simp
        ring
    _ ≤ 1445000 * (31 * Real.log B) := by
        exact mul_le_mul_of_nonneg_left hM'le (by norm_num)
    _ = 44795000 * Real.log B := by ring

/-- **Landau partial fraction, unit-disk form**: f analytic on the closed unit disk, f(0) = 1,
‖f‖ ≤ B on ‖z‖ ≤ 24/25 (2 ≤ B), finite zero set.  Then for ‖z‖ ≤ 83/100 with f(z) ≠ 0,
logDeriv f z is the sum of m_ρ/(z−ρ) over zeros with ‖ρ‖ ≤ 22/25, up to an error ≤ 44795000 log B. -/
theorem logDeriv_partial_fraction_unit {f : ℂ → ℂ} {B : ℝ}
    (hfa : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) (hf0 : f 0 = 1)
    (hfin : (SetOfZeros 1 f).Finite) (hB2 : 2 ≤ B)
    (hfB : ∀ w : ℂ, ‖w‖ ≤ 24/25 → ‖f w‖ ≤ B)
    {z : ℂ} (hz : ‖z‖ ≤ 83/100) (hfz : f z ≠ 0) :
    ‖logDeriv f z - ∑ ρ ∈ (finiteSetOfZeros_mono (by norm_num : (22/25:ℝ) < 1) hfin).toFinset,
        (analyticOrderNatAt f ρ : ℂ) / (z - ρ)‖ ≤ 44795000 * Real.log B := by
  have hf0' : f 0 ≠ 0 := by rw [hf0]; exact one_ne_zero
  have hsplit := logDeriv_split hfa hf0' (by norm_num : (22/25:ℝ) < 1) hfin
    (lt_of_le_of_lt hz (by norm_num)) hfz
  rw [hsplit]
  rw [add_sub_cancel_left]
  exact norm_logDeriv_Cf_le hfa hf0 hfin hB2 hfB hz

/-- The zero set of an analytic function (nonvanishing at the centre) in the closed unit ball is
finite. -/
lemma finite_SetOfZeros {f : ℂ → ℂ}
    (hfa : AnalyticOnNhd ℂ f (Metric.closedBall (0 : ℂ) 1)) (hf0 : f 0 ≠ 0) :
    (SetOfZeros 1 f).Finite := by
  set U := Metric.closedBall (0 : ℂ) 1 with hU
  have h0U : (0 : ℂ) ∈ U := by
    rw [hU, Metric.mem_closedBall, dist_self]
    norm_num
  have hcod : {z : ℂ | f z ≠ 0} ∈ Filter.codiscreteWithin U := by
    rcases hfa.eqOn_zero_or_eventually_ne_zero_of_preconnected
        (by rw [hU]; exact Metric.isPreconnected_closedBall) with h | h
    · exact absurd (h h0U) hf0
    · exact h
  rw [codiscreteWithin_iff_locallyFiniteComplementWithin] at hcod
  have hsub1 : Metric.closedBall (0 : ℂ) 1 ⊆ U := subset_rfl
  choose t ht htfin using fun z (hz : z ∈ Metric.closedBall (0:ℂ) 1) => hcod z (hsub1 hz)
  obtain ⟨s, hs⟩ := (isCompact_closedBall (0:ℂ) 1).elim_nhds_subcover'
    (fun z hz => t z hz) (fun z hz => ht z hz)
  refine Set.Finite.subset (Set.Finite.biUnion s.finite_toSet
    (fun z _ => htfin z.1 z.2)) ?_
  intro ρ hρ
  have hρball : ρ ∈ Metric.closedBall (0:ℂ) 1 := by
    rw [Metric.mem_closedBall, Complex.dist_eq, sub_zero]
    exact hρ.1
  obtain ⟨z, hz, hρz⟩ := Set.mem_iUnion₂.mp (hs hρball)
  refine Set.mem_biUnion hz ?_
  refine ⟨hρz, hsub1 hρball, ?_⟩
  simp only [Set.mem_setOf_eq, not_not]
  exact hρ.2

/-- **Landau partial fraction on a general disk** (affine rescaling of the unit version):
f analytic on a neighbourhood of closedBall s₀ R, f(s₀) ≠ 0, ‖f‖ ≤ B·‖f(s₀)‖ on the (24/25)R-ball,
2 ≤ B.  The zero set in the (22/25)R-ball is a finite set Z, and on the (83/100)R-ball (off zeros)
logDeriv f is Σ_{ρ ∈ Z} m_ρ/(s−ρ) up to 44795000·(log B)/R. -/
theorem logDeriv_partial_fraction_disk {f : ℂ → ℂ} {s₀ : ℂ} {R B : ℝ}
    (hR : 0 < R) (hfa : AnalyticOnNhd ℂ f (Metric.closedBall s₀ R)) (hf0 : f s₀ ≠ 0)
    (hB2 : 2 ≤ B) (hfB : ∀ w ∈ Metric.closedBall s₀ (24/25 * R), ‖f w‖ ≤ B * ‖f s₀‖) :
    ∃ Z : Finset ℂ,
      (↑Z = {ρ ∈ Metric.closedBall s₀ (22/25 * R) | f ρ = 0}) ∧
      ((∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ)) ≤ 1 / Real.log ((24/25) / (22/25)) * Real.log B) ∧
      ∀ s ∈ Metric.closedBall s₀ (83/100 * R), f s ≠ 0 →
        ‖logDeriv f s - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖
          ≤ 44795000 / R * Real.log B := by
  have hRC : (R : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hR
  set φ : ℂ → ℂ := fun w => s₀ + (R : ℂ) * w with hφ
  have hφmem : ∀ {w : ℂ} {r : ℝ}, ‖w‖ ≤ r → φ w ∈ Metric.closedBall s₀ (r * R) := by
    intro w r hw
    rw [Metric.mem_closedBall, Complex.dist_eq, hφ]
    simp only [add_sub_cancel_left]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    calc R * ‖w‖ ≤ R * r := mul_le_mul_of_nonneg_left hw hR.le
      _ = r * R := mul_comm _ _
  set c : ℂ := (f s₀)⁻¹ with hc
  have hcne : c ≠ 0 := inv_ne_zero hf0
  set g : ℂ → ℂ := fun w => c * f (φ w) with hg
  have hφa : ∀ w : ℂ, AnalyticAt ℂ φ w := fun w => by
    rw [hφ]
    exact analyticAt_const.add (analyticAt_const.mul analyticAt_id)
  have hφd : ∀ w : ℂ, deriv φ w = (R : ℂ) := by
    intro w
    rw [hφ]
    simp
  have hφinj : Function.Injective φ := by
    intro a b hab
    rw [hφ] at hab
    simp only [add_right_inj] at hab
    exact mul_left_cancel₀ hRC hab
  have hga : AnalyticOnNhd ℂ g (Metric.closedBall (0 : ℂ) 1) := by
    intro w hw
    have hwn : ‖w‖ ≤ 1 := by rwa [Metric.mem_closedBall, Complex.dist_eq, sub_zero] at hw
    have hmem : φ w ∈ Metric.closedBall s₀ R := by
      have := hφmem (r := 1) hwn
      simpa using this
    exact analyticAt_const.mul ((hfa (φ w) hmem).comp (hφa w))
  have hg0 : g 0 = 1 := by
    rw [hg, hc]
    simp only [hφ, mul_zero, add_zero]
    exact inv_mul_cancel₀ hf0
  have hg0' : g 0 ≠ 0 := by rw [hg0]; exact one_ne_zero
  have hfin : (SetOfZeros 1 g).Finite := finite_SetOfZeros hga hg0'
  have hgB : ∀ w : ℂ, ‖w‖ ≤ 24/25 → ‖g w‖ ≤ B := by
    intro w hw
    rw [hg]
    simp only
    rw [norm_mul, hc, norm_inv]
    rw [inv_mul_le_iff₀ (norm_pos_iff.mpr hf0)]
    calc ‖f (φ w)‖ ≤ B * ‖f s₀‖ := hfB (φ w) (hφmem hw)
      _ = ‖f s₀‖ * B := mul_comm _ _
  have hfnezero : ∀ ρg : ℂ, g ρg = 0 ↔ f (φ ρg) = 0 := by
    intro ρg
    rw [hg]
    simp only
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h | h
      · exact absurd h hcne
      · exact h
    · intro h
      rw [h, mul_zero]
  set Zg := (finiteSetOfZeros_mono (by norm_num : (22/25 : ℝ) < 1) hfin).toFinset with hZg
  have hZgmem : ∀ ρg : ℂ, ρg ∈ Zg ↔ (‖ρg‖ ≤ 22/25 ∧ f (φ ρg) = 0) := by
    intro ρg
    rw [hZg, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (hfnezero ρg).mp h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (hfnezero ρg).mpr h2⟩
  have hord : ∀ ρg : ℂ, ‖ρg‖ ≤ 1 → analyticOrderNatAt g ρg = analyticOrderNatAt f (φ ρg) := by
    intro ρg hρg
    have hcomp : analyticOrderAt (f ∘ φ) ρg = analyticOrderAt f (φ ρg) :=
      analyticOrderAt_comp_of_deriv_ne_zero (hφa ρg) (by rw [hφd]; exact hRC)
    have hsmul : analyticOrderAt g ρg = analyticOrderAt (f ∘ φ) ρg := by
      have heq : g = (fun _ : ℂ => c) • (f ∘ φ) := by
        funext w
        simp [hg, smul_eq_mul]
      rw [heq, analyticOrderAt_smul analyticAt_const
        (((hfa (φ ρg) (by simpa using hφmem (r := 1) hρg)).comp (hφa ρg)))]
      rw [(analyticAt_const (v := c)).analyticOrderAt_eq_zero.mpr hcne, zero_add]
    rw [analyticOrderNatAt, analyticOrderNatAt, hsmul, hcomp]
  refine ⟨Zg.image φ, ?_, ?_, ?_⟩
  · ext ρ
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe, Set.mem_setOf_eq]
    constructor
    · rintro ⟨ρg, hρg, rfl⟩
      obtain ⟨h1, h2⟩ := (hZgmem ρg).mp hρg
      exact ⟨by simpa using hφmem h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨(ρ - s₀) / (R : ℂ), ?_, ?_⟩
      · rw [hZgmem]
        constructor
        · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
            div_le_iff₀ hR]
          rw [Metric.mem_closedBall, Complex.dist_eq] at h1
          linarith [h1]
        · rw [show φ ((ρ - s₀) / (R:ℂ)) = ρ by rw [hφ]; field_simp; ring]
          exact h2
      · rw [hφ]; field_simp; ring
  · have hcount := ZerosBound (by norm_num) (by norm_num)
      (by norm_num : (22/25:ℝ) < 24/25) (by norm_num) hga hg0 hfin hgB
    rw [Finset.sum_image (fun a _ b _ hab => hφinj hab)]
    have hcongr : ∀ ρg ∈ Zg, (analyticOrderNatAt f (φ ρg) : ℝ) = (analyticOrderNatAt g ρg : ℝ) := by
      intro ρg hρg
      rw [hord ρg (le_trans ((hZgmem ρg).mp hρg).1 (by norm_num))]
    rw [Finset.sum_congr rfl hcongr]
    exact_mod_cast hcount
  · intro s hs hfs
    set w : ℂ := (s - s₀) / (R : ℂ) with hw
    have hφw : φ w = s := by rw [hφ, hw]; field_simp; ring
    have hwn : ‖w‖ ≤ 83/100 := by
      rw [hw, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR, div_le_iff₀ hR]
      rw [Metric.mem_closedBall, Complex.dist_eq] at hs
      linarith [hs]
    have hgw : g w ≠ 0 := by
      rw [hg]
      simp only
      rw [hφw]
      exact mul_ne_zero hcne hfs
    have hunit := logDeriv_partial_fraction_unit hga hg0 hfin hB2 hgB hwn hgw
    have hsR : s ∈ Metric.closedBall s₀ R :=
      Metric.closedBall_subset_closedBall (by nlinarith) hs
    have hld : logDeriv g w = (R : ℂ) * logDeriv f s := by
      have hstep : logDeriv g w = logDeriv (f ∘ φ) w := by
        rw [hg]
        exact logDeriv_const_mul w c hcne
      have hdf : DifferentiableAt ℂ f (φ w) := by
        rw [hφw]
        exact (hfa s hsR).differentiableAt
      rw [hstep, logDeriv_comp hdf (hφa w).differentiableAt, hφw, hφd, mul_comm]
    have hsum : ∑ ρ ∈ Zg.image φ, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)
        = (R : ℂ)⁻¹ * ∑ ρg ∈ Zg, (analyticOrderNatAt g ρg : ℂ) / (w - ρg) := by
      rw [Finset.sum_image (fun a _ b _ hab => hφinj hab), Finset.mul_sum]
      refine Finset.sum_congr rfl fun ρg hρg => ?_
      have h34 : ‖ρg‖ ≤ 22/25 := ((hZgmem ρg).mp hρg).1
      rw [hord ρg (by linarith)]
      have hsub : s - φ ρg = (R : ℂ) * (w - ρg) := by
        rw [← hφw, hφ]
        ring
      rw [hsub]
      rw [div_mul_eq_div_div_swap]
      field_simp
    rw [hsum]
    have hfld : logDeriv f s = (R:ℂ)⁻¹ * logDeriv g w := by
      rw [hld]
      field_simp
    rw [hfld, ← mul_sub, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hR]
    rw [div_eq_inv_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left hunit (inv_nonneg.mpr hR.le)


end UnitDisk

/-- **Partial fraction for ζ'/ζ at height t** (|t| ≥ 6): there is a finite set Z — exactly the
ζ-zeros within distance (22/25)·(91/50) of 2+it — such that on the ball of radius 3/2 around
2+it (covering 1/2 ≤ Re s ≤ 2 at height t), away from zeros,
ζ'/ζ(s) = Σ_{ρ ∈ Z} m_ρ/(s−ρ) + O(log(|t|+3)). -/
theorem zeta_logDeriv_partial_fraction : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 6 ≤ |t| →
    ∃ Z : Finset ℂ,
      (↑Z = {ρ ∈ Metric.closedBall (2 + t * I) (22/25 * (91/50)) | riemannZeta ρ = 0}) ∧
      ((∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ C * Real.log (|t| + 3)) ∧
      ∀ s ∈ Metric.closedBall (2 + t * I) (3/2), riemannZeta s ≠ 0 →
        ‖logDeriv riemannZeta s - ∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)‖
          ≤ C * Real.log (|t| + 3) := by
  obtain ⟨A, C₀, hC₀, hgrow⟩ := Zeta23.RvM.zeta_growth_quarter
  set A' : ℝ := max A 0 with hA'
  have hA'0 : 0 ≤ A' := le_max_right _ _
  have hCpos : (0:ℝ) < (44795000 * 50 / 91) * (Real.log 3 + Real.log (C₀ + 2) + A' + 1) := by
    have h1 : (0:ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have h2 : (0:ℝ) ≤ Real.log (C₀ + 2) := Real.log_nonneg (by linarith)
    positivity
  refine ⟨(44795000 * 50 / 91) * (Real.log 3 + Real.log (C₀ + 2) + A' + 1), hCpos,
    fun t ht => ?_⟩
  set s₀ : ℂ := 2 + t * I with hs₀
  have hs₀re : s₀.re = 2 := by simp [hs₀]
  have hs₀im : s₀.im = t := by simp [hs₀]
  have hζs₀ : riemannZeta s₀ ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by rw [hs₀re]; norm_num)
  have hlow : (1/3 : ℝ) ≤ ‖riemannZeta s₀‖ := Zeta23.RvM.zeta_lower_bound_two t
  -- analyticity on the closed ball of radius 91/50
  have hone : (1 : ℂ) ∉ Metric.closedBall s₀ (91/50) := by
    intro h
    rw [Metric.mem_closedBall, Complex.dist_eq] at h
    have him : ((1 : ℂ) - s₀).im = -t := by simp [hs₀]
    have : |t| ≤ ‖(1 : ℂ) - s₀‖ := by
      calc |t| = |((1:ℂ) - s₀).im| := by rw [him, abs_neg]
        _ ≤ ‖(1:ℂ) - s₀‖ := Complex.abs_im_le_norm _
    linarith
  have hfa : AnalyticOnNhd ℂ riemannZeta (Metric.closedBall s₀ (91/50)) :=
    Zeta23.RvM.analyticOnNhd_riemannZeta hone
  -- the B-bound on the (24/25)·(91/50)-ball
  set B : ℝ := 3 * (C₀ * (|t| + 2) ^ A' + 2) with hB
  have ht2 : (1:ℝ) ≤ |t| + 2 := by linarith
  have hpow1 : (1:ℝ) ≤ (|t| + 2) ^ A' := Real.one_le_rpow ht2 hA'0
  have hB2 : 2 ≤ B := by
    rw [hB]
    nlinarith [mul_nonneg hC₀.le (le_trans zero_le_one hpow1)]
  have hfB : ∀ w ∈ Metric.closedBall s₀ (24/25 * (91/50)), ‖riemannZeta w‖ ≤ B * ‖riemannZeta s₀‖ := by
    intro w hw
    rw [Metric.mem_closedBall, Complex.dist_eq] at hw
    have hwre : |w.re - 2| ≤ 24/25 * (91/50) := by
      have := Complex.abs_re_le_norm (w - s₀)
      have hre : (w - s₀).re = w.re - 2 := by simp [hs₀]
      rw [hre] at this
      linarith
    have hwim : |w.im - t| ≤ 24/25 * (91/50) := by
      have := Complex.abs_im_le_norm (w - s₀)
      have him : (w - s₀).im = w.im - t := by simp [hs₀]
      rw [him] at this
      linarith
    have hwim1 : 1 ≤ |w.im| := by
      have h3 : |t| - |w.im| ≤ |t - w.im| := abs_sub_abs_le_abs_sub t w.im
      have h4 : |t - w.im| = |w.im - t| := abs_sub_comm t w.im
      linarith [hwim]
    have hwimt : |w.im| ≤ |t| + 2 := by
      have := abs_sub_abs_le_abs_sub w.im t
      have h2 : |w.im| - |t| ≤ |w.im - t| := this
      linarith [hwim]
    have hbound : ‖riemannZeta w‖ ≤ C₀ * (|t| + 2) ^ A' + 2 := by
      rcases le_or_gt w.re 2 with hre2 | hre2
      · have h14 : (1/4 : ℝ) ≤ w.re := by
          rw [abs_le] at hwre
          linarith
        have := hgrow w h14 hre2 hwim1
        calc ‖riemannZeta w‖ ≤ C₀ * |w.im| ^ A := this
          _ ≤ C₀ * (|t| + 2) ^ A' := by
              refine mul_le_mul_of_nonneg_left ?_ hC₀.le
              calc |w.im| ^ A ≤ |w.im| ^ A' :=
                    Real.rpow_le_rpow_of_exponent_le hwim1 (le_max_left _ _)
                _ ≤ (|t| + 2) ^ A' := Real.rpow_le_rpow (by linarith) hwimt hA'0
          _ ≤ C₀ * (|t| + 2) ^ A' + 2 := by linarith
      · have := Zeta23.RvM.norm_riemannZeta_le_of_two_le_re (s := w) (by linarith)
        have hπ : (Real.pi : ℝ) ^ 2 / 6 ≤ 2 := by nlinarith [Real.pi_lt_d2, Real.pi_gt_three]
        calc ‖riemannZeta w‖ ≤ Real.pi ^ 2 / 6 := this
          _ ≤ 2 := hπ
          _ ≤ C₀ * (|t| + 2) ^ A' + 2 := by
              nlinarith [mul_nonneg hC₀.le (le_trans zero_le_one hpow1)]
    calc ‖riemannZeta w‖ ≤ C₀ * (|t| + 2) ^ A' + 2 := hbound
      _ = (B * (1/3)) := by rw [hB]; ring
      _ ≤ B * ‖riemannZeta s₀‖ := by
          refine mul_le_mul_of_nonneg_left hlow (by rw [hB]; positivity)
  obtain ⟨Z, hZset, hZcount, hZpf⟩ := logDeriv_partial_fraction_disk (f := riemannZeta)
    (by norm_num : (0:ℝ) < 91/50) hfa hζs₀ hB2 hfB
  -- logarithmic bookkeeping shared by the count bound and the partial-fraction bound
  have hT3 : (2:ℝ) ≤ Real.log (|t| + 3) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have h1 := Real.exp_one_lt_d9
    calc Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      _ ≤ 2.7182818286 * 2.7182818286 := by nlinarith [Real.exp_pos 1]
      _ ≤ 9 := by norm_num
      _ ≤ |t| + 3 := by linarith
  have hlogB : Real.log B ≤ (Real.log 3 + Real.log (C₀ + 2) + A') * Real.log (|t| + 3) := by
    have h1 : B ≤ 3 * ((C₀ + 2) * (|t| + 2) ^ A') := by
      rw [hB]
      nlinarith [hpow1, hC₀]
    have h2 : Real.log B ≤ Real.log (3 * ((C₀ + 2) * (|t| + 2) ^ A')) :=
      Real.log_le_log (by rw [hB]; positivity) h1
    rw [Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (by positivity),
      Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (by positivity),
      Real.log_mul (by positivity : (C₀ + 2 : ℝ) ≠ 0) (by positivity),
      Real.log_rpow (by linarith : (0:ℝ) < |t| + 2)] at h2
    have h3 : Real.log (|t| + 2) ≤ Real.log (|t| + 3) :=
      Real.log_le_log (by linarith) (by linarith)
    have h4 : (0:ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have h5 : (0:ℝ) ≤ Real.log (C₀ + 2) := Real.log_nonneg (by linarith)
    have hBeq : Real.log B = Real.log 3 + Real.log (C₀ * (|t| + 2) ^ A' + 2) := by
      rw [hB, Real.log_mul (by norm_num : (3:ℝ) ≠ 0) (by positivity)]
    rw [hBeq]
    nlinarith [mul_nonneg hA'0 (by linarith : (0:ℝ) ≤ Real.log (|t|+3) - Real.log (|t|+2)),
      mul_nonneg h4 (by linarith : (0:ℝ) ≤ Real.log (|t|+3) - 1),
      mul_nonneg h5 (by linarith : (0:ℝ) ≤ Real.log (|t|+3) - 1), hT3]
  have h4 : (0:ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have h5 : (0:ℝ) ≤ Real.log (C₀ + 2) := Real.log_nonneg (by linarith)
  refine ⟨Z, ?_, ?_, ?_⟩
  · rw [hZset]
  · refine hZcount.trans ?_
    have hratio : ((24/25 : ℝ))/(22/25) = 12/11 := by norm_num
    have hlog1211 : (1:ℝ)/12 ≤ Real.log ((24/25)/(22/25)) := by
      rw [hratio]
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 11/12 by norm_num)
      rw [show (11/12:ℝ) = (12/11)⁻¹ by norm_num, Real.log_inv] at h
      linarith
    have hlogpos : (0:ℝ) < Real.log ((24/25)/(22/25)) := by
      rw [hratio]
      exact Real.log_pos (by norm_num)
    have hlogBnn : (0:ℝ) ≤ Real.log B := Real.log_nonneg (by linarith)
    calc 1 / Real.log ((24/25)/(22/25)) * Real.log B ≤ 12 * Real.log B := by
          refine mul_le_mul_of_nonneg_right ?_ hlogBnn
          rw [div_le_iff₀ hlogpos]
          linarith
      _ ≤ 12 * ((Real.log 3 + Real.log (C₀ + 2) + A') * Real.log (|t| + 3)) :=
          mul_le_mul_of_nonneg_left hlogB (by norm_num)
      _ ≤ 44795000 * 50 / 91 * (Real.log 3 + Real.log (C₀ + 2) + A' + 1) * Real.log (|t| + 3) := by
          nlinarith [hT3, hA'0]
  · intro s hs hζs
    have hs' : s ∈ Metric.closedBall s₀ (83/100 * (91/50)) :=
      Metric.closedBall_subset_closedBall (by norm_num) hs
    refine (hZpf s hs' hζs).trans ?_
    calc 44795000 / (91/50) * Real.log B
        ≤ 44795000 / (91/50) * ((Real.log 3 + Real.log (C₀ + 2) + A') * Real.log (|t| + 3)) :=
          mul_le_mul_of_nonneg_left hlogB (by norm_num)
      _ ≤ (44795000 * 50 / 91) * (Real.log 3 + Real.log (C₀ + 2) + A' + 1) * Real.log (|t| + 3) := by
          nlinarith [hT3, hA'0]


end WeilEF
end Zeta23
