/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/ZeroCount/Generic.lean — the zero-counting templates with Y := ξ′/Γℝ abstracted to an
arbitrary f (the Hardy-W development instantiates f := hardyW).

INPUT DATA ("two-line data" for f about the line Re s = 2):
  hfa   : for |t| ≥ t₀, f is analytic on a neighbourhood of closedBall (2+it) (91/50);
  hgrow : ‖f s‖ ≤ Cf·|Im s|^k on 1/8 ≤ Re s ≤ 4, |Im s| ≥ 2;
  hlow' : ‖f(2+it)‖ ≥ 1 for |t| ≥ t₀.
OUTPUTS:
  logDeriv_partial_fraction_two_line — Landau: zero finset in the 22/25·91/50-ball, Σ ord ≤ C log(|t|+3), and
      f′/f = Σ ord/(s−ρ) + O(log(|t|+3)) on the 3/2-ball (|t| ≥ t₁ := max t₀ 4);
  horizontal_bound_two_line — |Im ∫_{1/2}^{2} f′/f(σ+iT)dσ| ≤ C log(|T|+3) whenever no right-half-plane zero of f
      has ordinate T;
  local_count_two_line — for a ZeroConfig Zc whose points with β ≥ 1/2 are zeros of f of the same order:
      N(t,t+1] ≤ A₀ log(|t|+3) for all t;
  good_heights_two_line — if moreover every right-half-plane zero of f with |Im| ≥ t₀ is in Zc: for j ≥ j₀ some
      R ∈ [j,j+1] has f ≠ 0, ‖f′/f‖ ≤ C log²(j+3) on Im s = ±R, 1/2 ≤ Re s ≤ 2.
(ZeroCount/{Landau,Sides,GoodHeights}.lean derive the f = Yfn := ξ′/Γℝ instances from these.)
-/
import Zeta23.XiPrime.ZeroCount.Basic
import Zeta23.XiPrime.ZeroCount.ArgBound
import Zeta23.WeilEF.Landau
import Zeta23.WeilEF.GoodHeights

open Complex Set Filter Topology MeasureTheory intervalIntegral Metric
open scoped ComplexConjugate

noncomputable section

namespace Zeta23
namespace XiPrime
namespace ZeroCount
namespace Generic

/-- **Landau partial fraction about 2+it, generic.** -/
theorem logDeriv_partial_fraction_two_line {f : ℂ → ℂ} {Cf t₀ : ℝ} {k : ℕ}
    (hfa : ∀ t : ℝ, t₀ ≤ |t| → AnalyticOnNhd ℂ f (closedBall (2 + t * I) (91 / 50)))
    (hCf : 0 < Cf)
    (hgrow : ∀ s : ℂ, 1 / 8 ≤ s.re → s.re ≤ 4 → 2 ≤ |s.im| → ‖f s‖ ≤ Cf * |s.im| ^ k)
    (hlow' : ∀ t : ℝ, t₀ ≤ |t| → 1 ≤ ‖f (2 + t * I)‖) :
    ∃ C t₁ : ℝ, 0 < C ∧ 4 ≤ t₁ ∧ t₀ ≤ t₁ ∧ ∀ t : ℝ, t₁ ≤ |t| →
    f (2 + t * I) ≠ 0 ∧
    ∃ Z : Finset ℂ,
      (↑Z = {ρ ∈ closedBall (2 + t * I) (22 / 25 * (91 / 50)) | f ρ = 0}) ∧
      ((∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ)) ≤ C * Real.log (|t| + 3)) ∧
      ∀ s ∈ closedBall (2 + t * I) (3 / 2), f s ≠ 0 →
        ‖logDeriv f s - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖
          ≤ C * Real.log (|t| + 3) := by
  set CY := Cf with hCYdef
  have hCY : 0 < CY := hCf
  set C' : ℝ := CY + 2 with hC'
  have hC'2 : 2 ≤ C' := by rw [hC']; linarith
  have hlogC' : 0 ≤ Real.log C' := Real.log_nonneg (by linarith)
  set C : ℝ := (44795000 * 50 / 91) * (Real.log C' + k) with hC
  have hCpos : 0 < C := by
    rw [hC]
    have : 0 < Real.log C' + k := by
      have : 0 < Real.log C' := Real.log_pos (by linarith)
      positivity
    positivity
  refine ⟨C, max t₀ 4, hCpos, le_max_right _ _, le_max_left _ _, fun t ht => ?_⟩
  have ht₁ : t₀ ≤ |t| := le_trans (le_max_left _ _) ht
  have ht4 : 4 ≤ |t| := le_trans (le_max_right _ _) ht
  set s₀ : ℂ := 2 + t * I with hs₀
  have hY0 : 1 ≤ ‖f s₀‖ := hlow' t ht₁
  have hne : f s₀ ≠ 0 := by
    intro h; rw [h, norm_zero] at hY0; linarith
  have hfa : AnalyticOnNhd ℂ f (closedBall s₀ (91 / 50)) := hfa t ht₁
  set B : ℝ := C' * (|t| + 2) ^ k with hB
  have hpow1 : (1 : ℝ) ≤ (|t| + 2) ^ k := one_le_pow₀ (by linarith [abs_nonneg t])
  have hB2 : 2 ≤ B := by
    rw [hB]; nlinarith
  have hfB : ∀ w ∈ closedBall s₀ (24 / 25 * (91 / 50)), ‖f w‖ ≤ B * ‖f s₀‖ := by
    intro w hw
    rw [mem_closedBall, Complex.dist_eq] at hw
    have hwre : |w.re - 2| ≤ 24 / 25 * (91 / 50) := by
      have := Complex.abs_re_le_norm (w - s₀)
      have hre : (w - s₀).re = w.re - 2 := by simp [hs₀]
      rw [hre] at this; linarith
    have hwim : |w.im - t| ≤ 24 / 25 * (91 / 50) := by
      have := Complex.abs_im_le_norm (w - s₀)
      have him : (w - s₀).im = w.im - t := by simp [hs₀]
      rw [him] at this; linarith
    rw [abs_le] at hwre hwim
    have h1 : (1 / 8 : ℝ) ≤ w.re := by linarith [hwre.1]
    have h2 : w.re ≤ 4 := by linarith [hwre.2]
    have h3 : 2 ≤ |w.im| := by
      rcases le_abs'.mp ht4 with h | h
      · rw [abs_of_neg (by linarith [hwim.2])]; linarith [hwim.2]
      · rw [abs_of_pos (by linarith [hwim.1])]; linarith [hwim.1]
    have h4 : |w.im| ≤ |t| + 2 := by
      have := abs_sub_abs_le_abs_sub w.im t
      have h5 : |w.im - t| ≤ 2 := abs_le.mpr ⟨by linarith [hwim.1], by linarith [hwim.2]⟩
      linarith
    calc ‖f w‖ ≤ CY * |w.im| ^ k := hgrow w h1 h2 h3
      _ ≤ CY * (|t| + 2) ^ k := by gcongr
      _ ≤ C' * (|t| + 2) ^ k := by gcongr; linarith
      _ = B * 1 := by rw [hB]; ring
      _ ≤ B * ‖f s₀‖ := by gcongr
  obtain ⟨Z, hZset, hZcount, hZpf⟩ := Zeta23.WeilEF.logDeriv_partial_fraction_disk (f := f)
    (by norm_num : (0:ℝ) < 91 / 50) hfa hne hB2 hfB
  have hlog3 := one_le_log_add_three t
  have hlogB : Real.log B ≤ (Real.log C' + k) * Real.log (|t| + 3) := by
    rw [hB, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have h1 : Real.log (|t| + 2) ≤ Real.log (|t| + 3) :=
      Real.log_le_log (by linarith [abs_nonneg t]) (by linarith)
    have h0 : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
    have h2 : Real.log C' ≤ Real.log C' * Real.log (|t| + 3) := le_mul_of_one_le_right hlogC' hlog3
    have h3 : (k : ℝ) * Real.log (|t| + 2) ≤ (k : ℝ) * Real.log (|t| + 3) :=
      mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg k)
    linarith
  have hlogBnn : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
  refine ⟨hne, Z, hZset, ?_, ?_⟩
  · refine hZcount.trans ?_
    have hratio : ((24 / 25 : ℝ)) / (22 / 25) = 12 / 11 := by norm_num
    have hlogpos : (0:ℝ) < Real.log ((24 / 25) / (22 / 25)) := by
      rw [hratio]; exact Real.log_pos (by norm_num)
    have hlog1211 : (1:ℝ) / 12 ≤ Real.log ((24 / 25) / (22 / 25)) := by
      rw [hratio]
      have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 11 / 12 by norm_num)
      rw [show (11 / 12 : ℝ) = (12 / 11)⁻¹ by norm_num, Real.log_inv] at h
      linarith
    calc 1 / Real.log ((24 / 25) / (22 / 25)) * Real.log B ≤ 12 * Real.log B := by
          refine mul_le_mul_of_nonneg_right ?_ hlogBnn
          rw [div_le_iff₀ hlogpos]; linarith
      _ ≤ 12 * ((Real.log C' + k) * Real.log (|t| + 3)) := by gcongr
      _ ≤ C * Real.log (|t| + 3) := by
          rw [hC]
          have : (0:ℝ) ≤ (Real.log C' + k) * Real.log (|t| + 3) := by positivity
          nlinarith
  · intro s hs hYs
    have hs' : s ∈ closedBall s₀ (83 / 100 * (91 / 50)) :=
      closedBall_subset_closedBall (by norm_num) hs
    refine (hZpf s hs' hYs).trans ?_
    calc 44795000 / (91 / 50) * Real.log B
        ≤ 44795000 / (91 / 50) * ((Real.log C' + k) * Real.log (|t| + 3)) := by gcongr
      _ = C * Real.log (|t| + 3) := by rw [hC]; ring


/-- **Horizontal sides, generic**: with the data of `logDeriv_partial_fraction_two_line`, for every T with
|T| ≥ t₁ such that no zero of f in the right half-plane has ordinate T,
|Im ∫_{1/2}^{2} f′/f(σ+iT) dσ| ≤ C·log(|T|+3). -/
theorem horizontal_bound_two_line {f : ℂ → ℂ} {Cf t₀ : ℝ} {k : ℕ}
    (hfa : ∀ t : ℝ, t₀ ≤ |t| → AnalyticOnNhd ℂ f (closedBall (2 + t * I) (91 / 50)))
    (hCf : 0 < Cf)
    (hgrow : ∀ s : ℂ, 1 / 8 ≤ s.re → s.re ≤ 4 → 2 ≤ |s.im| → ‖f s‖ ≤ Cf * |s.im| ^ k)
    (hlow' : ∀ t : ℝ, t₀ ≤ |t| → 1 ≤ ‖f (2 + t * I)‖) :
    ∃ C t₁ : ℝ, 0 < C ∧ 4 ≤ t₁ ∧ t₀ ≤ t₁ ∧ ∀ T : ℝ, t₁ ≤ |T| →
    (∀ ρ : ℂ, 0 < ρ.re → f ρ = 0 → ρ.im ≠ T) →
    |(∫ σ in (1 / 2 : ℝ)..2, logDeriv f (σ + T * I)).im| ≤ C * Real.log (|T| + 3) := by
  classical
  obtain ⟨C, t₁, hC, ht₁, ht₀, hpf⟩ := logDeriv_partial_fraction_two_line hfa hCf hgrow hlow'
  refine ⟨5 * C, t₁, by positivity, ht₁, ht₀, fun T hT hgood => ?_⟩
  obtain ⟨-, Z, hZset, hZcount, hZpf⟩ := hpf T hT
  have hfaT := hfa T (le_trans ht₀ hT)
  set s₀ : ℂ := 2 + T * I with hs₀
  have hL := Real.log_nonneg (by linarith [abs_nonneg T] : (1:ℝ) ≤ |T| + 3)
  -- facts at segment points
  have hseg : ∀ σ ∈ Icc (1 / 2 : ℝ) 2,
      ((σ : ℂ) + T * I) ∈ closedBall s₀ (3 / 2) ∧ 0 < ((σ : ℂ) + T * I).re ∧ f ((σ : ℂ) + T * I) ≠ 0 := by
    intro σ hσ
    have hre : ((σ : ℂ) + T * I).re = σ := by simp
    refine ⟨?_, by rw [hre]; linarith [hσ.1], ?_⟩
    · rw [mem_closedBall, Complex.dist_eq]
      have : (σ : ℂ) + T * I - s₀ = ((σ - 2 : ℝ) : ℂ) := by
        simp [hs₀]
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hσ.1, hσ.2]
    · intro h0
      exact hgood _ (by rw [hre]; linarith [hσ.1]) h0 (by simp)
  -- zeros in Z are zeros of ξ′, hence off the line Im = T
  have hZoff : ∀ ρ ∈ Z, ∀ σ ∈ Icc (1 / 2 : ℝ) 2, (σ : ℂ) + T * I ≠ ρ := by
    intro ρ hρ σ _ hEq
    have hρ' : ρ ∈ (↑Z : Set ℂ) := hρ
    rw [hZset] at hρ'
    obtain ⟨hρball, hρ0⟩ := hρ'
    have hρre : 0 < ρ.re := by
      rw [mem_closedBall, Complex.dist_eq] at hρball
      have := Complex.abs_re_le_norm (ρ - s₀)
      have e : (ρ - s₀).re = ρ.re - 2 := by simp [hs₀]
      rw [e, abs_le] at this
      linarith [this.1]
    exact hgood ρ hρre hρ0 (by rw [← hEq]; simp)
  have hZoff' : ∀ ρ ∈ Z, ∀ σ ∈ uIcc (1 / 2 : ℝ) 2, (σ : ℂ) + T * I ≠ ρ := by
    rw [uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 2)]; exact hZoff
  -- the partial-fraction sum along the segment and the remainder
  set PF : ℝ → ℂ := fun σ => ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / ((σ : ℂ) + T * I - ρ) with hPF
  set E : ℝ → ℂ := fun σ => logDeriv f ((σ : ℂ) + T * I) - PF σ with hE
  have hEbound : ∀ σ ∈ Set.uIoc (1 / 2 : ℝ) 2, ‖E σ‖ ≤ C * Real.log (|T| + 3) := by
    intro σ hσ
    have hσ' : σ ∈ Icc (1 / 2 : ℝ) 2 := by
      rw [uIoc_of_le (by norm_num : (1/2:ℝ) ≤ 2)] at hσ
      exact ⟨hσ.1.le, hσ.2⟩
    obtain ⟨hball, _, hY⟩ := hseg σ hσ'
    exact hZpf _ hball hY
  -- continuity / integrability
  have hcontLD : ContinuousOn (fun σ : ℝ => logDeriv f ((σ : ℂ) + T * I)) (uIcc (1 / 2 : ℝ) 2) := by
    intro σ hσ
    rw [uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 2)] at hσ
    obtain ⟨hball, hre, hY⟩ := hseg σ hσ
    have ha : AnalyticAt ℂ f ((σ : ℂ) + T * I) :=
      hfaT _ (closedBall_subset_closedBall (by norm_num) hball)
    have hc : ContinuousAt (logDeriv f) ((σ : ℂ) + T * I) := by
      have := (ha.deriv.continuousAt).div ha.continuousAt hY
      simpa only [logDeriv] using this
    exact (hc.comp (f := fun σ : ℝ => (σ : ℂ) + T * I) (by fun_prop)).continuousWithinAt
  have hintLD : IntervalIntegrable (fun σ : ℝ => logDeriv f ((σ : ℂ) + T * I)) volume (1 / 2) 2 :=
    hcontLD.intervalIntegrable
  have hintTerm : ∀ ρ ∈ Z, IntervalIntegrable
      (fun σ : ℝ => (analyticOrderNatAt f ρ : ℂ) / ((σ : ℂ) + T * I - ρ)) volume (1 / 2) 2 := by
    intro ρ hρ
    have := (intervalIntegrable_inv_sub (hZoff' ρ hρ)).const_mul (analyticOrderNatAt f ρ : ℂ)
    exact this.congr fun σ _ => by simp [div_eq_mul_inv]
  have hintPF : IntervalIntegrable PF volume (1 / 2) 2 := by
    have := IntervalIntegrable.sum Z hintTerm
    exact this.congr fun σ _ => by simp [hPF, Finset.sum_apply]
  have hintE : IntervalIntegrable E volume (1 / 2) 2 := hintLD.sub hintPF
  -- split the integral
  have hsplit : (∫ σ in (1 / 2 : ℝ)..2, logDeriv f ((σ : ℂ) + T * I))
      = (∫ σ in (1 / 2 : ℝ)..2, PF σ) + ∫ σ in (1 / 2 : ℝ)..2, E σ := by
    rw [← integral_add hintPF hintE]
    apply integral_congr
    intro σ _
    simp [hE]
  -- the partial-fraction part: Im = Σ m_ρ · Im ∫ (s−ρ)⁻¹, each |·| ≤ π
  have hPFint : (∫ σ in (1 / 2 : ℝ)..2, PF σ)
      = ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) * ∫ σ in (1 / 2 : ℝ)..2, ((σ : ℂ) + T * I - ρ)⁻¹ := by
    simp only [hPF]
    rw [integral_finset_sum hintTerm]
    refine Finset.sum_congr rfl (fun ρ _ => ?_)
    simp only [div_eq_mul_inv]
    exact intervalIntegral.integral_const_mul _ _
  have hPFim : |(∫ σ in (1 / 2 : ℝ)..2, PF σ).im| ≤ Real.pi * (C * Real.log (|T| + 3)) := by
    rw [hPFint, Complex.im_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ ρ ∈ Z, |((analyticOrderNatAt f ρ : ℂ)
        * ∫ σ in (1 / 2 : ℝ)..2, ((σ : ℂ) + T * I - ρ)⁻¹).im|
        ≤ (analyticOrderNatAt f ρ : ℝ) * Real.pi := by
      intro ρ hρ
      have him : ((analyticOrderNatAt f ρ : ℂ) * ∫ σ in (1 / 2 : ℝ)..2, ((σ : ℂ) + T * I - ρ)⁻¹).im
          = (analyticOrderNatAt f ρ : ℝ) * (∫ σ in (1 / 2 : ℝ)..2, ((σ : ℂ) + T * I - ρ)⁻¹).im := by
        rw [Complex.mul_im]; simp
      rw [him, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul_of_nonneg_left
        (abs_im_integral_inv_sub_le_pi (by norm_num) T ρ (hZoff ρ hρ)) (Nat.cast_nonneg _)
    calc ∑ ρ ∈ Z, |((analyticOrderNatAt f ρ : ℂ)
            * ∫ σ in (1 / 2 : ℝ)..2, ((σ : ℂ) + T * I - ρ)⁻¹).im|
        ≤ ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ) * Real.pi := Finset.sum_le_sum hterm
      _ = Real.pi * ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ) := by rw [Finset.mul_sum]; simp [mul_comm]
      _ ≤ Real.pi * (C * Real.log (|T| + 3)) := mul_le_mul_of_nonneg_left hZcount Real.pi_pos.le
  -- the remainder part
  have hEim : |(∫ σ in (1 / 2 : ℝ)..2, E σ).im| ≤ 3 / 2 * (C * Real.log (|T| + 3)) := by
    refine (Complex.abs_im_le_norm _).trans ?_
    have := intervalIntegral.norm_integral_le_of_norm_le_const hEbound
    calc ‖∫ σ in (1 / 2 : ℝ)..2, E σ‖ ≤ C * Real.log (|T| + 3) * |2 - 1 / 2| := this
      _ = 3 / 2 * (C * Real.log (|T| + 3)) := by norm_num; ring
  rw [hsplit, Complex.add_im]
  calc |(∫ σ in (1 / 2 : ℝ)..2, PF σ).im + (∫ σ in (1 / 2 : ℝ)..2, E σ).im|
      ≤ |(∫ σ in (1 / 2 : ℝ)..2, PF σ).im| + |(∫ σ in (1 / 2 : ℝ)..2, E σ).im| := abs_add_le _ _
    _ ≤ Real.pi * (C * Real.log (|T| + 3)) + 3 / 2 * (C * Real.log (|T| + 3)) := add_le_add hPFim hEim
    _ ≤ 5 * C * Real.log (|T| + 3) := by
        have h0 : 0 ≤ C * Real.log (|T| + 3) := by positivity
        have hπ : Real.pi ≤ 3.5 := by linarith [Real.pi_lt_d2]
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 3.5 - Real.pi) h0]


/-! ### local count -/

/-- the β ≥ 1/2 half of the window (t, t+1] counted with multiplicity is ≪ log(|t|+3), for |t + 1/2| ≥ t₁. -/
theorem half_count_large_two_line {f : ℂ → ℂ} {Cf t₀ : ℝ} {k : ℕ}
    (hfa : ∀ t : ℝ, t₀ ≤ |t| → AnalyticOnNhd ℂ f (closedBall (2 + t * I) (91 / 50)))
    (hCf : 0 < Cf)
    (hgrow : ∀ s : ℂ, 1 / 8 ≤ s.re → s.re ≤ 4 → 2 ≤ |s.im| → ‖f s‖ ≤ Cf * |s.im| ^ k)
    (hlow' : ∀ t : ℝ, t₀ ≤ |t| → 1 ≤ ‖f (2 + t * I)‖)
    (Zc : ZeroConfig)
    (hlink : ∀ ρ ∈ Zc.carrier, 1 / 2 ≤ ρ.re → f ρ = 0 ∧ analyticOrderNatAt f ρ = Zc.mult ρ) :
    ∃ A₁ t₁ : ℝ, 0 < A₁ ∧ ∀ t : ℝ, t₁ ≤ |t + 1 / 2| →
    (∑ᶠ ρ ∈ Zc.window t (t + 1) ∩ {ρ | 1 / 2 ≤ ρ.re}, (Zc.mult ρ : ℝ)) ≤ A₁ * Real.log (|t| + 3) := by
  classical
  obtain ⟨C, t₁, hC, ht₁4, -, hpf⟩ := logDeriv_partial_fraction_two_line hfa hCf hgrow hlow'
  refine ⟨2 * C, t₁, by positivity, fun t ht => ?_⟩
  obtain ⟨-, Z, hZset, hZcount, -⟩ := hpf (t + 1 / 2) ht
  set W : Set ℂ := Zc.window t (t + 1) ∩ {ρ | 1 / 2 ≤ ρ.re} with hW
  have hWfin : W.Finite := (Zc.window_finite t (t + 1)).subset inter_subset_left
  -- every ρ ∈ W is a zero of Y within 22/25·91/50 of the centre, with the same multiplicity
  have hmem : ∀ ρ ∈ W, ρ ∈ Z := by
    rintro ρ ⟨⟨hρ0, hρ1, hρ2⟩, hρre⟩
    have hstrip := Zc.strip ρ hρ0
    have hre : (1 / 2 : ℝ) ≤ ρ.re := hρre
    rw [← Finset.mem_coe, hZset]
    refine ⟨?_, (hlink ρ hρ0 hre).1⟩
    rw [mem_closedBall, Complex.dist_eq]
    have hre' : (ρ - (2 + ((t + 1 / 2 : ℝ) : ℂ) * I)).re = ρ.re - 2 := by simp
    have him' : (ρ - (2 + ((t + 1 / 2 : ℝ) : ℂ) * I)).im = ρ.im - (t + 1 / 2) := by simp
    have hsq : ‖ρ - (2 + ((t + 1 / 2 : ℝ) : ℂ) * I)‖ ^ 2 ≤ (5 / 2 : ℝ) := by
      rw [Complex.sq_norm, Complex.normSq_apply, hre', him']
      nlinarith [hstrip.2]
    nlinarith [norm_nonneg (ρ - (2 + ((t + 1 / 2 : ℝ) : ℂ) * I))]
  have hmult : ∀ ρ ∈ W, (Zc.mult ρ : ℝ) = (analyticOrderNatAt f ρ : ℝ) := by
    rintro ρ ⟨⟨hρ0, -, -⟩, hρre⟩
    rw [(hlink ρ hρ0 hρre).2]
  have hsum : (∑ᶠ ρ ∈ W, (Zc.mult ρ : ℝ))
      ≤ ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ hWfin,
      Finset.sum_congr rfl (fun ρ hρ => hmult ρ (hWfin.mem_toFinset.mp hρ))]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ρ hρ
      exact hmem ρ (hWfin.mem_toFinset.mp hρ)
    · intros; positivity
  have hlog : Real.log (|t + 1 / 2| + 3) ≤ 2 * Real.log (|t| + 3) := by
    have h1 : |t + 1 / 2| + 3 ≤ (|t| + 3) ^ 2 := by
      have := abs_add_le t (1 / 2)
      rw [abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)] at this
      nlinarith [abs_nonneg t]
    calc Real.log (|t + 1 / 2| + 3) ≤ Real.log ((|t| + 3) ^ 2) :=
          Real.log_le_log (by positivity) h1
      _ = 2 * Real.log (|t| + 3) := by rw [Real.log_pow]; push_cast; ring
  calc (∑ᶠ ρ ∈ W, (Zc.mult ρ : ℝ)) ≤ _ := hsum
    _ ≤ C * Real.log (|t + 1 / 2| + 3) := hZcount
    _ ≤ C * (2 * Real.log (|t| + 3)) := by gcongr
    _ = 2 * C * Real.log (|t| + 3) := by ring

/-- **Local count, generic**: N(t,t+1] ≤ A₀ log(|t|+3) for every real t, for a ZeroConfig linked to f. -/
theorem local_count_two_line {f : ℂ → ℂ} {Cf t₀ : ℝ} {k : ℕ}
    (hfa : ∀ t : ℝ, t₀ ≤ |t| → AnalyticOnNhd ℂ f (closedBall (2 + t * I) (91 / 50)))
    (hCf : 0 < Cf)
    (hgrow : ∀ s : ℂ, 1 / 8 ≤ s.re → s.re ≤ 4 → 2 ≤ |s.im| → ‖f s‖ ≤ Cf * |s.im| ^ k)
    (hlow' : ∀ t : ℝ, t₀ ≤ |t| → 1 ≤ ‖f (2 + t * I)‖)
    (Zc : ZeroConfig)
    (hlink : ∀ ρ ∈ Zc.carrier, 1 / 2 ≤ ρ.re → f ρ = 0 ∧ analyticOrderNatAt f ρ = Zc.mult ρ) :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ t : ℝ,
    (Zc.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3) := by
  obtain ⟨A₁, t₁, hA₁, hlarge⟩ := half_count_large_two_line hfa hCf hgrow hlow' Zc hlink
  -- the finite constant for small |t|
  set K : ℝ := (Zc.N (-(|t₁| + 2)) (|t₁| + 2) : ℝ) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨max 1 (max (2 * A₁) K), le_max_left _ _, fun t => ?_⟩
  have hlog3 := one_le_log_add_three t
  rcases le_or_gt t₁ |t + 1 / 2| with ht | ht
  · have hhalf := Zc.N_le_two_mul_half t (t + 1)
    calc (Zc.N t (t + 1) : ℝ) ≤ 2 * (A₁ * Real.log (|t| + 3)) := by
          refine hhalf.trans ?_
          have := hlarge t ht
          linarith
      _ = (2 * A₁) * Real.log (|t| + 3) := by ring
      _ ≤ max 1 (max (2 * A₁) K) * Real.log (|t| + 3) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          exact le_trans (le_max_left _ _) (le_max_right _ _)
  · -- |t + 1/2| < t₁ ≤ |t₁|: the window sits inside (−(|t₁|+2), |t₁|+2]
    have ht' : |t + 1 / 2| < |t₁| := lt_of_lt_of_le ht (le_abs_self _)
    rw [abs_lt] at ht'
    have hsub : Zc.window t (t + 1) ⊆ Zc.window (-(|t₁| + 2)) (|t₁| + 2) := by
      rintro ρ ⟨hρ, ha, hb⟩
      exact ⟨hρ, by linarith, by linarith⟩
    have hmono : Zc.N t (t + 1) ≤ Zc.N (-(|t₁| + 2)) (|t₁| + 2) :=
      Zc.finsum_mult_mono _ _ hsub subset_rfl
    calc (Zc.N t (t + 1) : ℝ) ≤ K := by rw [hK]; exact_mod_cast hmono
      _ ≤ K * Real.log (|t| + 3) := le_mul_of_one_le_right hK0 hlog3
      _ ≤ max 1 (max (2 * A₁) K) * Real.log (|t| + 3) := by
          apply mul_le_mul_of_nonneg_right _ (by linarith)
          exact le_trans (le_max_right _ _) (le_max_right _ _)


/-! ### good heights -/

set_option maxHeartbeats 1600000 in
/-- **Good heights, generic**: with the two-line data for f and a ZeroConfig Zc whose β ≥ 1/2 points are zeros
of f with the same order (hlink) and which contains every right-half-plane zero of f with |Im ρ| ≥ t₀ (hlink'):
for j ≥ j₀ there is R ∈ [j, j+1] with f ≠ 0 and ‖f′/f‖ ≤ C log²(j+3) on Im s = ±R, 1/2 ≤ Re s ≤ 2. -/
theorem good_heights_two_line {f : ℂ → ℂ} {Cf t₀ : ℝ} {k : ℕ}
    (hfa : ∀ t : ℝ, t₀ ≤ |t| → AnalyticOnNhd ℂ f (closedBall (2 + t * I) (91 / 50)))
    (hCf : 0 < Cf)
    (hgrow : ∀ s : ℂ, 1 / 8 ≤ s.re → s.re ≤ 4 → 2 ≤ |s.im| → ‖f s‖ ≤ Cf * |s.im| ^ k)
    (hlow' : ∀ t : ℝ, t₀ ≤ |t| → 1 ≤ ‖f (2 + t * I)‖)
    (Zc : ZeroConfig)
    (hlink : ∀ ρ ∈ Zc.carrier, 1 / 2 ≤ ρ.re → f ρ = 0 ∧ analyticOrderNatAt f ρ = Zc.mult ρ)
    (hlink' : ∀ ρ : ℂ, 0 < ρ.re → t₀ ≤ |ρ.im| → f ρ = 0 → ρ ∈ Zc.carrier) :
    ∃ C : ℝ, 0 < C ∧ ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j →
    ∃ R : ℝ, (j : ℝ) ≤ R ∧ R ≤ (j : ℝ) + 1 ∧
    ∀ s : ℂ, (s.im = R ∨ s.im = -R) → 1 / 2 ≤ s.re → s.re ≤ 2 →
      f s ≠ 0 ∧ ‖logDeriv f s‖ ≤ C * (Real.log ((j : ℝ) + 3)) ^ 2 := by
  classical
  obtain ⟨C, t₁, hC, ht₁4, ht₀, hpf⟩ := logDeriv_partial_fraction_two_line hfa hCf hgrow hlow'
  obtain ⟨A₀, hA₀1, hloc⟩ := local_count_two_line hfa hCf hgrow hlow' Zc hlink
  have hA₀ : 0 ≤ A₀ := by linarith
  -- the constant and the threshold
  refine ⟨2 * C * (48 * A₀ + 3), by positivity, ⌈t₁⌉₊ + 4, fun j hj => ?_⟩
  have hjt4 : t₁ + 4 ≤ j := by
    have h1 : t₁ ≤ ⌈t₁⌉₊ := Nat.le_ceil t₁
    have h2 : ((⌈t₁⌉₊ + 4 : ℕ) : ℝ) ≤ j := by exact_mod_cast hj
    push_cast at h2; linarith
  have hjt : t₁ ≤ j := by
    have h1 : t₁ ≤ ⌈t₁⌉₊ := Nat.le_ceil t₁
    have h2 : ((⌈t₁⌉₊ + 4 : ℕ) : ℝ) ≤ j := by exact_mod_cast hj
    push_cast at h2; linarith
  have hj4 : (4 : ℝ) ≤ j := by
    have h2 : ((⌈t₁⌉₊ + 4 : ℕ) : ℝ) ≤ j := by exact_mod_cast hj
    push_cast at h2; linarith [Nat.cast_nonneg (α := ℝ) ⌈t₁⌉₊]
  set Lg : ℝ := Real.log ((j : ℝ) + 3) with hLg
  have hLg1 : 1 ≤ Lg := by
    rw [hLg, ← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith
  have hlog2 : Real.log 2 ≤ Lg := by rw [hLg]; exact Real.log_le_log (by norm_num) (by linarith)
  -- the two finite families of zeros near height ±j (as sets of ℂ)
  set Wp : Set ℂ := Zc.window ((j : ℝ) - 3) ((j : ℝ) - 3 + (6 : ℕ)) with hWp
  set Wm : Set ℂ := Zc.window (-(j : ℝ) - 4) (-(j : ℝ) - 4 + (6 : ℕ)) with hWm
  have hWpfin : Wp.Finite := Zc.window_finite _ _
  have hWmfin : Wm.Finite := Zc.window_finite _ _
  set S : Finset ℝ := hWpfin.toFinset.image (fun ρ : ℂ => ρ.im)
    ∪ hWmfin.toFinset.image (fun ρ : ℂ => -ρ.im) with hS
  -- counts
  have hwin6 : ∀ a : ℝ, |a| ≤ (j : ℝ) + 4 → (Zc.N a (a + (6 : ℕ)) : ℝ) ≤ 6 * (A₀ * (2 * Lg)) := by
    intro a ha
    rw [N_unit_windows Zc a 6, Nat.cast_sum]
    have hterm : ∀ i ∈ Finset.range 6, (Zc.N (a + i) (a + i + 1) : ℝ) ≤ A₀ * (2 * Lg) := by
      intro i hi
      have hi6 : (i : ℝ) < 6 := by exact_mod_cast Finset.mem_range.mp hi
      refine (hloc (a + i)).trans (mul_le_mul_of_nonneg_left ?_ hA₀)
      have h1 : |a + i| + 3 ≤ ((j : ℝ) + 3) ^ 2 := by
        have := abs_add_le a (i : ℝ)
        rw [Nat.abs_cast] at this
        nlinarith
      calc Real.log (|a + ↑i| + 3) ≤ Real.log (((j : ℝ) + 3) ^ 2) :=
            Real.log_le_log (by positivity) h1
        _ = 2 * Lg := by rw [hLg, Real.log_pow]; push_cast; ring
    calc ∑ i ∈ Finset.range 6, (Zc.N (a + i) (a + i + 1) : ℝ)
        ≤ ∑ i ∈ Finset.range 6, A₀ * (2 * Lg) := Finset.sum_le_sum hterm
      _ = 6 * (A₀ * (2 * Lg)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
  have hcardW : ∀ {W : Set ℂ} (hW : W.Finite) (a : ℝ), W = Zc.window a (a + (6 : ℕ)) →
      |a| ≤ (j : ℝ) + 4 → (hW.toFinset.card : ℝ) ≤ 6 * (A₀ * (2 * Lg)) := by
    intro W hW a hWa ha
    have h1 : hW.toFinset.card = W.ncard := (Set.ncard_eq_toFinset_card W hW).symm
    have h2 : W.ncard ≤ Zc.N a (a + (6 : ℕ)) := by
      rw [hWa]; exact Zc.ncard_le_finsum_mult a (a + (6 : ℕ)) subset_rfl
    calc (hW.toFinset.card : ℝ) = (W.ncard : ℝ) := by rw [h1]
      _ ≤ (Zc.N a (a + (6 : ℕ)) : ℝ) := by exact_mod_cast h2
      _ ≤ 6 * (A₀ * (2 * Lg)) := hwin6 a ha
  have hcard : (S.card : ℝ) ≤ 24 * A₀ * Lg := by
    have h1 : S.card ≤ hWpfin.toFinset.card + hWmfin.toFinset.card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)
    have h1' : (S.card : ℝ) ≤ hWpfin.toFinset.card + hWmfin.toFinset.card := by exact_mod_cast h1
    have hp := hcardW hWpfin ((j : ℝ) - 3) hWp (by rw [abs_of_nonneg (by linarith)]; linarith)
    have hm := hcardW hWmfin (-(j : ℝ) - 4) hWm (by rw [abs_of_nonpos (by linarith)]; linarith)
    linarith
  -- the good height
  obtain ⟨R, hR1, hR2, hfar⟩ := Zeta23.WeilEF.exists_far_point S j
  set δ : ℝ := 1 / (2 * ((S.card : ℝ) + 1)) with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hδinv : 1 / δ = 2 * ((S.card : ℝ) + 1) := by rw [hδ, one_div_one_div]
  refine ⟨R, hR1, hR2, ?_⟩
  have hlogR : Real.log (|R| + 3) ≤ 2 * Lg := by
    rw [abs_of_nonneg (by linarith)]
    calc Real.log (R + 3) ≤ Real.log (2 * ((j:ℝ) + 3)) := Real.log_le_log (by linarith) (by linarith)
      _ = Real.log 2 + Lg := by rw [Real.log_mul (by norm_num) (by linarith)]
      _ ≤ 2 * Lg := by linarith
  -- the right half 1/2 ≤ Re s ≤ 2
  have right_half : ∀ s : ℂ, (s.im = R ∨ s.im = -R) → 1 / 2 ≤ s.re → s.re ≤ 2 →
      f s ≠ 0 ∧ ‖logDeriv f s‖ ≤ (2 * C * (48 * A₀ + 3)) * Lg ^ 2 := by
    intro s hsR hσ1 hσ2
    have hsre : 0 < s.re := by linarith
    have habs : |s.im| = R := by
      rcases hsR with h | h
      · rw [h, abs_of_nonneg (by linarith)]
      · rw [h, abs_neg, abs_of_nonneg (by linarith)]
    have ht : t₁ ≤ |s.im| := by rw [habs]; linarith
    obtain ⟨_, Z, hZset, hZsum, hZpf⟩ := hpf s.im ht
    have hsball : s ∈ closedBall (2 + s.im * I) (3 / 2) := by
      rw [mem_closedBall, dist_eq_norm]
      have : s - (2 + s.im * I) = ((s.re - 2 : ℝ) : ℂ) := by apply Complex.ext <;> simp
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (by linarith)]
      linarith
    -- every zero of Y in the pf ball has its signed ordinate in S, hence is δ-far from s
    have hordS : ∀ ρ : ℂ, ρ ∈ closedBall (2 + s.im * I) (22 / 25 * (91 / 50)) →
        f ρ = 0 → δ ≤ ‖s - ρ‖ := by
      intro ρ hρ hz
      have him := Zeta23.WeilEF.im_mem_of_mem_closedBall hρ
      rw [mem_closedBall, dist_eq_norm] at hρ
      have hρre : 0 < ρ.re := by
        have := Complex.abs_re_le_norm (ρ - (2 + s.im * I))
        simp at this; rw [abs_le] at this; linarith [this.1]
      have hρim : t₀ ≤ |ρ.im| := by
        have h1 : |ρ.im - s.im| ≤ 22 / 25 * (91 / 50) := him
        have h2 := abs_sub_abs_le_abs_sub s.im ρ.im
        rw [abs_sub_comm] at h2
        rw [habs] at h2
        linarith
      have hρc : ρ ∈ Zc.carrier := hlink' ρ hρre hρim hz
      rw [abs_le] at him
      refine le_trans ?_ (Zeta23.WeilEF.abs_im_sub_le_norm_sub s ρ)
      rcases hsR with hsR | hsR
      · have hmem : ρ ∈ hWpfin.toFinset := by
          rw [Set.Finite.mem_toFinset, hWp]
          rw [hsR] at him
          refine ⟨hρc, ?_, ?_⟩
          · show (j : ℝ) - 3 < ρ.im
            linarith [him.1]
          · show ρ.im ≤ (j : ℝ) - 3 + ((6 : ℕ) : ℝ)
            push_cast; linarith [him.2]
        have : ρ.im ∈ S := by
          rw [hS, Finset.mem_union]; left
          exact Finset.mem_image.mpr ⟨ρ, hmem, rfl⟩
        have := hfar _ this
        rwa [hsR]
      · have hmem : ρ ∈ hWmfin.toFinset := by
          rw [Set.Finite.mem_toFinset, hWm]
          rw [hsR] at him
          refine ⟨hρc, ?_, ?_⟩
          · show -(j : ℝ) - 4 < ρ.im
            linarith [him.1]
          · show ρ.im ≤ -(j : ℝ) - 4 + ((6 : ℕ) : ℝ)
            push_cast; linarith [him.2]
        have : -ρ.im ∈ S := by
          rw [hS, Finset.mem_union]; right
          exact Finset.mem_image.mpr ⟨ρ, hmem, rfl⟩
        have := hfar _ this
        rw [hsR, show |(-R) - ρ.im| = |R - (-ρ.im)| by rw [← abs_neg]; ring_nf]
        exact this
    have hY : f s ≠ 0 := by
      intro hz
      have h0 := hordS s (closedBall_subset_closedBall (by norm_num) hsball) hz
      simp at h0; linarith
    refine ⟨hY, ?_⟩
    have hZpf' := hZpf s hsball hY
    have hlogt : Real.log (|s.im| + 3) ≤ 2 * Lg := by rw [habs]; rw [abs_of_nonneg (by linarith)] at hlogR; exact hlogR
    have hZmem : ∀ ρ ∈ Z, ρ ∈ closedBall (2 + s.im * I) (22 / 25 * (91 / 50)) ∧ f ρ = 0 := by
      intro ρ hρ
      have : ρ ∈ (↑Z : Set ℂ) := hρ
      rw [hZset] at this
      exact this
    have hsumZ : ‖∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ ≤ (C * (2 * Lg)) * (1 / δ) := by
      calc ‖∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖
          ≤ ∑ ρ ∈ Z, ‖(analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ := norm_sum_le _ _
        _ ≤ ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ) * (1 / δ) := by
            refine Finset.sum_le_sum fun ρ hρ => ?_
            obtain ⟨hρb, hρz⟩ := hZmem ρ hρ
            have hd := hordS ρ hρb hρz
            rw [norm_div, Complex.norm_natCast, div_eq_mul_one_div]
            refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
            exact one_div_le_one_div_of_le hδpos hd
        _ = (∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℝ)) * (1 / δ) := by rw [Finset.sum_mul]
        _ ≤ (C * (2 * Lg)) * (1 / δ) := by
            refine mul_le_mul_of_nonneg_right (hZsum.trans ?_) (div_nonneg zero_le_one hδpos.le)
            exact mul_le_mul_of_nonneg_left hlogt hC.le
    have hYld : ‖logDeriv f s‖ ≤ C * (2 * Lg) + (C * (2 * Lg)) * (1 / δ) := by
      have h1 : ‖logDeriv f s‖
          ≤ ‖logDeriv f s - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖
            + ‖∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ := norm_le_norm_sub_add _ _
      have h2 := hZpf'.trans (mul_le_mul_of_nonneg_left hlogt hC.le)
      linarith [hsumZ]
    refine hYld.trans ?_
    rw [hδinv]
    have : C * (2 * Lg) + C * (2 * Lg) * (2 * ((S.card : ℝ) + 1))
        = 2 * C * Lg * (2 * (S.card : ℝ) + 3) := by ring
    rw [this]
    have hn : 2 * (S.card : ℝ) + 3 ≤ (48 * A₀ + 3) * Lg := by nlinarith
    calc 2 * C * Lg * (2 * (S.card : ℝ) + 3) ≤ 2 * C * Lg * ((48 * A₀ + 3) * Lg) :=
          mul_le_mul_of_nonneg_left hn (by positivity)
      _ = 2 * C * (48 * A₀ + 3) * Lg ^ 2 := by ring
  exact right_half


end Generic
end ZeroCount
end XiPrime
end Zeta23
