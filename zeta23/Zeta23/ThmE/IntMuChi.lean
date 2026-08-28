/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmE/IntMuChi.lean — the [eq:muints]-type integrals for μ_χ: the
int_mu / int_mu_sq fields of GammaFactsChi κ q.

Route: the proofs are generic in the function — with explicit
constants (`int_g_explicit`, `int_g_sq_explicit`; the ∃-forms and the fixed-q μ_χ forms are their corollaries)
for an arbitrary continuous g with |g(τ) − (1/2π)log(|τ|/2π)| ≤ C/τ² (section Generic). Then μ_χ = g + (log q)/(2π) with
g := μ_χ − (log q)/(2π), since the conductor cancels in the Stirling field:
  μ_χ(τ) − (1/2π)log(q|τ|/2π) = g(τ) − (1/2π)log(|τ|/2π),
and ell1q q T = ell1 T + log q, so
  ∫_T^{2T} μ_χ = T·ell1q/(2π) + O(1/T),   ∫_T^{2T} μ_χ² = (T·ell1q²/4π²)(1 + O(l⁻²)).
-/
import Zeta23.ThmE.Hypotheses
import Zeta23.GammaFacts.IntMu

noncomputable section

namespace Zeta23
namespace ThmE
namespace IntMuChi

open MeasureTheory intervalIntegral

section Generic

variable {g : ℝ → ℝ}

/-- Explicit-constant form of `int_g_of_stirling` (constants depend only on the Stirling constant C). -/
theorem int_g_explicit (hcont : Continuous g) {C : ℝ}
    (hC : ∀ τ : ℝ, 1 ≤ |τ| →
      |g τ - (1 / (2 * Real.pi)) * Real.log (|τ| / (2 * Real.pi))| ≤ C / τ ^ 2)
    {T : ℝ} (hT : 1 ≤ T) :
    |(∫ τ in T..(2 * T), g τ) - T * ell1 T / (2 * Real.pi)| ≤ C / T := by
  have hC0 : 0 ≤ C := by
    have h := hC 1 (by norm_num)
    have := abs_nonneg (g 1 - 1 / (2 * Real.pi) * Real.log (|1| / (2 * Real.pi)))
    nlinarith
  have hμcont : Continuous g := hcont
  have hT0 : (0 : ℝ) < T := by linarith
  -- split μ = main + error on [T, 2T]
  have hint_mu : IntervalIntegrable g volume T (2 * T) :=
    hμcont.intervalIntegrable _ _
  have hint_main : IntervalIntegrable
      (fun τ : ℝ => (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) volume T (2 * T) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    refine ContinuousOn.mul continuousOn_const ?_
    intro τ hτ
    have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le hT0 hτ.1
    exact ((Real.continuousAt_log (by positivity)).comp
      (continuousAt_id.div_const _)).continuousWithinAt
  have hsplit : (∫ τ in T..(2 * T), g τ)
      = (∫ τ in T..(2 * T), (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi)))
        + ∫ τ in T..(2 * T),
            (g τ - (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) := by
    rw [← intervalIntegral.integral_add hint_main (hint_mu.sub hint_main)]
    congr 1
    funext τ
    ring
  rw [hsplit, MuInts.integral_main_eq hT0]
  rw [add_sub_cancel_left]
  -- bound the error integral
  have herr_int : IntervalIntegrable
      (fun τ : ℝ => g τ - (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi)))
      volume T (2 * T) := hint_mu.sub hint_main
  have hbound : ∀ τ ∈ Set.Icc T (2 * T),
      |g τ - (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))| ≤ C / τ ^ 2 := by
    intro τ hτ
    have hτ1 : (1 : ℝ) ≤ τ := le_trans hT hτ.1
    have habs : |τ| = τ := abs_of_pos (by linarith)
    have h := hC τ (by rwa [habs])
    rwa [habs] at h
  have hCtau : IntervalIntegrable (fun τ : ℝ => C / τ ^ 2) volume T (2 * T) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    intro τ hτ
    have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le hT0 hτ.1
    exact (continuousAt_const.div (continuousAt_pow _ _) (by positivity)).continuousWithinAt
  have hCint : ∫ τ in T..(2 * T), C / τ ^ 2 = C / (2 * T) := by
    have hftc2 : ∀ τ ∈ Set.uIcc T (2 * T),
        HasDerivAt (fun x : ℝ => -C / x) (C / τ ^ 2) τ := by
      intro τ hτ
      rw [Set.uIcc_of_le (by linarith)] at hτ
      have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le hT0 hτ.1
      have hinv : HasDerivAt (fun x : ℝ => x⁻¹) (-1 / τ ^ 2) τ := (hasDerivAt_id τ).inv hτ0.ne'
      have h1 := hinv.const_mul (-C)
      have h3 : (fun x : ℝ => -C * x⁻¹) = fun x : ℝ => -C / x := by
        funext x
        ring
      rw [h3] at h1
      have heq : -C * (-1 / τ ^ 2) = C / τ ^ 2 := by ring
      rw [heq] at h1
      exact h1
    rw [integral_eq_sub_of_hasDerivAt hftc2 hCtau]
    field_simp
    ring
  calc |∫ τ in T..(2 * T),
        (g τ - (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi)))|
      ≤ ∫ τ in T..(2 * T),
          |g τ - (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))| :=
        intervalIntegral.abs_integral_le_integral_abs (by linarith)
    _ ≤ ∫ τ in T..(2 * T), C / τ ^ 2 := by
        refine intervalIntegral.integral_mono_on (by linarith) herr_int.abs hCtau ?_
        intro τ hτ
        exact hbound τ hτ
    _ = C / (2 * T) := hCint
    _ ≤ C / T := by
        have h2 : (0 : ℝ) < 2 * T := by linarith
        rw [div_le_div_iff₀ h2 hT0]
        nlinarith


set_option maxHeartbeats 1600000 in
/-- Explicit-constant form of `int_g_sq_of_stirling` (constants depend only on the Stirling constant C). -/
theorem int_g_sq_explicit (hcont : Continuous g) {C : ℝ}
    (hC : ∀ τ : ℝ, 1 ≤ |τ| →
      |g τ - (1 / (2 * Real.pi)) * Real.log (|τ| / (2 * Real.pi))| ≤ C / τ ^ 2)
    {T : ℝ} (hT : max (2 * Real.pi * Real.exp 4) (32 * Real.pi ^ 2 * (C * (1 + C) + 1)) ≤ T) :
    |(∫ τ in T..(2 * T), g τ ^ 2) - T * ell1 T ^ 2 / (4 * Real.pi ^ 2)|
      ≤ (8 * (1 + 2 * Real.log 2 ^ 2) + 1) * (T * ell1 T ^ 2 / (4 * Real.pi ^ 2)) / l T ^ 2 := by
  have hC0 : 0 ≤ C := by
    have h := hC 1 (by norm_num)
    have := abs_nonneg (g 1 - 1 / (2 * Real.pi) * Real.log (|1| / (2 * Real.pi)))
    nlinarith
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hμcont : Continuous g := hcont
  set C₂ : ℝ := C * (1 + C) + 1 with hC₂
  have hC₂0 : (0 : ℝ) < C₂ := by nlinarith
  set m : ℝ := Real.log 2 with hm
  have hm0 : (0 : ℝ) < m := Real.log_pos (by norm_num)
  have hm1 : m < 1 := by
    rw [hm]
    have := Real.log_two_lt_d9
    linarith
  have hT1 : 2 * Real.pi * Real.exp 4 ≤ T := le_trans (le_max_left _ _) hT
  have hT2 : 32 * Real.pi ^ 2 * C₂ ≤ T := le_trans (le_max_right _ _) hT
  have hexp1 : (1 : ℝ) ≤ Real.exp 4 := by
    have := Real.add_one_le_exp (4 : ℝ)
    linarith
  have hT0 : (0 : ℝ) < T := by nlinarith [Real.exp_pos (4 : ℝ)]
  have hL4 : (4 : ℝ) ≤ l T := by
    unfold l
    rw [show (4 : ℝ) = Real.log (Real.exp 4) from (Real.log_exp 4).symm]
    apply Real.log_le_log (Real.exp_pos 4)
    rw [le_div_iff₀ (by positivity)]
    linarith
  set L : ℝ := l T with hLdef
  have hL0 : (0 : ℝ) < L := by linarith
  have hL_le_T : L ≤ T := by
    rw [hLdef]
    unfold l
    have h1 := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < T / (2 * Real.pi))
    have h2 : T / (2 * Real.pi) ≤ T := by
      rw [div_le_iff₀ (by positivity)]
      have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
      nlinarith
    linarith
  have hell : ell1 T = L + 2 * m - 1 := by
    unfold ell1
    rw [← hLdef, ← hm]
  have hell_pos : (0 : ℝ) < ell1 T := by
    rw [hell]
    nlinarith
  have hell_ge : L / 2 ≤ ell1 T := by
    rw [hell]
    nlinarith
  have hell2 : L ^ 2 / 4 ≤ ell1 T ^ 2 := by
    nlinarith [hell_ge, hL0, hell_pos]
  have hmain_bound : ∀ τ ∈ Set.Icc T (2 * T),
      |(1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))| ≤ (L + m) / (2 * Real.pi) := by
    intro τ hτ
    have hτT : T ≤ τ := hτ.1
    have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le hT0 hτT
    have hlog_nonneg : (0 : ℝ) ≤ Real.log (τ / (2 * Real.pi)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have hlog_le : Real.log (τ / (2 * Real.pi)) ≤ L + m := by
      have h1 : Real.log (τ / (2 * Real.pi)) ≤ Real.log (2 * T / (2 * Real.pi)) := by
        apply Real.log_le_log (by positivity)
        gcongr
        exact hτ.2
      have h2 : Real.log (2 * T / (2 * Real.pi)) = m + L := by
        rw [show 2 * T / (2 * Real.pi) = 2 * (T / (2 * Real.pi)) by ring,
          Real.log_mul (by norm_num) (by positivity), hm, hLdef]
        rfl
      linarith
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi)),
      abs_of_nonneg hlog_nonneg]
    rw [one_div, div_eq_mul_inv (L + m), mul_comm (L + m)]
    exact mul_le_mul_of_nonneg_left hlog_le (by positivity)
  have herr_bound : ∀ τ ∈ Set.Icc T (2 * T),
      |g τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2|
        ≤ C / τ ^ 2 * (2 * ((L + m) / (2 * Real.pi)) + C) := by
    intro τ hτ
    have hτT : T ≤ τ := hτ.1
    have hτ1 : (1 : ℝ) ≤ τ := by nlinarith
    have habs : |τ| = τ := abs_of_pos (by linarith)
    have herr := hC τ (by rwa [habs])
    rw [habs] at herr
    have hmb := hmain_bound τ hτ
    have hsq : g τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2
        = (g τ - (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi)))
          * (g τ + (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) := by
      ring
    rw [hsq, abs_mul]
    have hτ2 : (0 : ℝ) < τ ^ 2 := by positivity
    have hCτ : C / τ ^ 2 ≤ C := by
      rw [div_le_iff₀ hτ2]
      have hτsq1 : (1 : ℝ) ≤ τ ^ 2 := by nlinarith
      nlinarith
    have hsum_bound : |g τ + (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))|
        ≤ 2 * ((L + m) / (2 * Real.pi)) + C := by
      have h4 := abs_sub_abs_le_abs_sub (g τ)
        ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi)))
      have h5 : |g τ - (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))| ≤ C :=
        le_trans herr hCτ
      have h3 : |g τ| ≤ (L + m) / (2 * Real.pi) + C := by linarith
      calc |g τ + (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))|
          ≤ |g τ| + |(1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))| :=
            abs_add_le _ _
        _ ≤ 2 * ((L + m) / (2 * Real.pi)) + C := by linarith
    exact mul_le_mul herr hsum_bound (abs_nonneg _) (by positivity)
  have hint_mu2 : IntervalIntegrable (fun τ : ℝ => g τ ^ 2) volume T (2 * T) :=
    (hμcont.pow 2).intervalIntegrable _ _
  have hint_main2 : IntervalIntegrable
      (fun τ : ℝ => ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2)
      volume T (2 * T) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    intro τ hτ
    have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le hT0 hτ.1
    exact ((continuousAt_const.mul ((Real.continuousAt_log (by positivity)).comp
      (continuousAt_id.div_const _))).pow 2).continuousWithinAt
  have hCtau2 : IntervalIntegrable
      (fun τ : ℝ => C / τ ^ 2 * (2 * ((L + m) / (2 * Real.pi)) + C)) volume T (2 * T) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    intro τ hτ
    have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le hT0 hτ.1
    exact ((continuousAt_const.div (continuousAt_pow _ _) (by positivity)).mul
      continuousAt_const).continuousWithinAt
  have hmain2 : ∫ τ in T..(2 * T), ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2
      = (1 / (4 * Real.pi ^ 2)) * (T * (ell1 T ^ 2 + 1 - 2 * m ^ 2)) := by
    rw [show (fun τ : ℝ => ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2)
        = fun τ : ℝ => (1 / (4 * Real.pi ^ 2)) * Real.log (τ / (2 * Real.pi)) ^ 2
      from funext fun τ => by field_simp; ring]
    rw [intervalIntegral.integral_const_mul, MuInts.integral_main_sq_eq hT0, hm]
  have hsplit : (∫ τ in T..(2 * T), g τ ^ 2)
      = (∫ τ in T..(2 * T), ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2)
        + ∫ τ in T..(2 * T),
            (g τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2) := by
    rw [← intervalIntegral.integral_add hint_main2 (hint_mu2.sub hint_main2)]
    congr 1
    funext τ
    ring
  have hCint : ∫ τ in T..(2 * T), C / τ ^ 2 = C / (2 * T) := by
    have hftc2 : ∀ τ ∈ Set.uIcc T (2 * T),
        HasDerivAt (fun x : ℝ => -C / x) (C / τ ^ 2) τ := by
      intro τ hτ
      rw [Set.uIcc_of_le (by linarith)] at hτ
      have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le hT0 hτ.1
      have hinv : HasDerivAt (fun x : ℝ => x⁻¹) (-1 / τ ^ 2) τ :=
        (hasDerivAt_id τ).inv hτ0.ne'
      have h1 := hinv.const_mul (-C)
      have h3 : (fun x : ℝ => -C * x⁻¹) = fun x : ℝ => -C / x := by
        funext x
        ring
      rw [h3] at h1
      have heq : -C * (-1 / τ ^ 2) = C / τ ^ 2 := by ring
      rw [heq] at h1
      exact h1
    have hCtau : IntervalIntegrable (fun τ : ℝ => C / τ ^ 2) volume T (2 * T) := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le (by linarith)]
      intro τ hτ
      have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le hT0 hτ.1
      exact (continuousAt_const.div (continuousAt_pow _ _)
        (by positivity)).continuousWithinAt
    rw [integral_eq_sub_of_hasDerivAt hftc2 hCtau]
    field_simp
    ring
  have herrI : |∫ τ in T..(2 * T),
      (g τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2)|
      ≤ (C / (2 * T)) * (2 * ((L + m) / (2 * Real.pi)) + C) := by
    have hCint2 : ∫ τ in T..(2 * T), C / τ ^ 2 * (2 * ((L + m) / (2 * Real.pi)) + C)
        = (C / (2 * T)) * (2 * ((L + m) / (2 * Real.pi)) + C) := by
      rw [show (fun τ : ℝ => C / τ ^ 2 * (2 * ((L + m) / (2 * Real.pi)) + C))
          = fun τ : ℝ => (2 * ((L + m) / (2 * Real.pi)) + C) * (C / τ ^ 2)
        from funext fun τ => by ring]
      rw [intervalIntegral.integral_const_mul, hCint]
      ring
    calc |∫ τ in T..(2 * T),
          (g τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2)|
        ≤ ∫ τ in T..(2 * T),
            |g τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2| :=
          intervalIntegral.abs_integral_le_integral_abs (by linarith)
      _ ≤ ∫ τ in T..(2 * T), C / τ ^ 2 * (2 * ((L + m) / (2 * Real.pi)) + C) := by
          refine intervalIntegral.integral_mono_on (by linarith)
            (hint_mu2.sub hint_main2).abs hCtau2 ?_
          intro τ hτ
          exact herr_bound τ hτ
      _ = (C / (2 * T)) * (2 * ((L + m) / (2 * Real.pi)) + C) := hCint2
  rw [hsplit, hmain2]
  set X : ℝ := T * ell1 T ^ 2 / (4 * Real.pi ^ 2) / L ^ 2 with hX
  have hX1 : T / (16 * Real.pi ^ 2) ≤ X := by
    rw [hX, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hell2, hT0.le, sq_nonneg L, mul_pos hT0 (mul_pos hπ hπ)]
  have hX0 : (0 : ℝ) < X := by
    rw [hX]
    positivity
  have htri : |(1 / (4 * Real.pi ^ 2)) * (T * (ell1 T ^ 2 + 1 - 2 * m ^ 2))
      + (∫ τ in T..(2 * T),
          (g τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2))
      - T * ell1 T ^ 2 / (4 * Real.pi ^ 2)|
      ≤ |(1 / (4 * Real.pi ^ 2)) * (T * (ell1 T ^ 2 + 1 - 2 * m ^ 2))
          - T * ell1 T ^ 2 / (4 * Real.pi ^ 2)|
        + |∫ τ in T..(2 * T),
            (g τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2)| := by
    have h1 := abs_add_le
      ((1 / (4 * Real.pi ^ 2)) * (T * (ell1 T ^ 2 + 1 - 2 * m ^ 2))
        - T * ell1 T ^ 2 / (4 * Real.pi ^ 2))
      (∫ τ in T..(2 * T),
        (g τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2))
    calc |(1 / (4 * Real.pi ^ 2)) * (T * (ell1 T ^ 2 + 1 - 2 * m ^ 2))
        + (∫ τ in T..(2 * T),
            (g τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2))
        - T * ell1 T ^ 2 / (4 * Real.pi ^ 2)|
        = |((1 / (4 * Real.pi ^ 2)) * (T * (ell1 T ^ 2 + 1 - 2 * m ^ 2))
            - T * ell1 T ^ 2 / (4 * Real.pi ^ 2))
          + ∫ τ in T..(2 * T),
              (g τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2)| := by
          congr 1
          ring
      _ ≤ _ := h1
  have hmain_dev : |(1 / (4 * Real.pi ^ 2)) * (T * (ell1 T ^ 2 + 1 - 2 * m ^ 2))
      - T * ell1 T ^ 2 / (4 * Real.pi ^ 2)|
      ≤ 8 * (1 + 2 * m ^ 2) * X := by
    have h1 : (1 / (4 * Real.pi ^ 2)) * (T * (ell1 T ^ 2 + 1 - 2 * m ^ 2))
        - T * ell1 T ^ 2 / (4 * Real.pi ^ 2) = T * (1 - 2 * m ^ 2) / (4 * Real.pi ^ 2) := by
      ring
    rw [h1, abs_div, abs_mul, abs_of_pos hT0,
      abs_of_pos (by positivity : (0 : ℝ) < 4 * Real.pi ^ 2)]
    have habs1 : |1 - 2 * m ^ 2| ≤ 1 + 2 * m ^ 2 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg m]
    calc T * |1 - 2 * m ^ 2| / (4 * Real.pi ^ 2)
        ≤ T * (1 + 2 * m ^ 2) / (4 * Real.pi ^ 2) := by gcongr
      _ = 4 * (1 + 2 * m ^ 2) * (T / (16 * Real.pi ^ 2)) := by ring
      _ ≤ 4 * (1 + 2 * m ^ 2) * X := by
          gcongr
      _ ≤ 8 * (1 + 2 * m ^ 2) * X := by nlinarith [hX0, sq_nonneg m]
  have herr_final : (C / (2 * T)) * (2 * ((L + m) / (2 * Real.pi)) + C) ≤ 1 * X := by
    have hπ3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hb1 : 2 * ((L + m) / (2 * Real.pi)) ≤ L := by
      have h2a : (L + m) / (2 * Real.pi) ≤ (L + 1) / (2 * Real.pi) := by
        gcongr
      have h2b : (L + 1) / (2 * Real.pi) ≤ (L + 1) / 6 :=
        div_le_div_of_nonneg_left (by linarith) (by norm_num) (by nlinarith)
      have h3 : (L + 1) / 6 ≤ L / 2 := by
        rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
        nlinarith
      linarith
    have hb2 : 2 * ((L + m) / (2 * Real.pi)) + C ≤ (1 + C) * L := by
      have h4 : C ≤ C * L := by nlinarith
      nlinarith
    have hb3 : (C / (2 * T)) * (2 * ((L + m) / (2 * Real.pi)) + C) ≤ C₂ * L / T := by
      have h5 : (0 : ℝ) ≤ 2 * ((L + m) / (2 * Real.pi)) + C := by positivity
      have h6 : (C / (2 * T)) * (2 * ((L + m) / (2 * Real.pi)) + C)
          ≤ (C / (2 * T)) * ((1 + C) * L) := by
        apply mul_le_mul_of_nonneg_left hb2 (by positivity)
      calc (C / (2 * T)) * (2 * ((L + m) / (2 * Real.pi)) + C)
          ≤ (C / (2 * T)) * ((1 + C) * L) := h6
        _ = (C * (1 + C)) * L / (2 * T) := by ring
        _ ≤ C₂ * L / T := by
            rw [div_le_div_iff₀ (by linarith) (by linarith)]
            have h7 : (0 : ℝ) ≤ C * (1 + C) := by nlinarith
            nlinarith [mul_nonneg (mul_nonneg h7 hL0.le) hT0.le, hL0.le, hT0.le]
    have hb4 : C₂ * L / T ≤ C₂ := by
      rw [div_le_iff₀ hT0]
      nlinarith
    have hb5 : C₂ ≤ T / (32 * Real.pi ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have hb6 : T / (32 * Real.pi ^ 2) ≤ T / (16 * Real.pi ^ 2) := by
      apply div_le_div_of_nonneg_left hT0.le (by positivity)
      nlinarith
    rw [one_mul]
    calc (C / (2 * T)) * (2 * ((L + m) / (2 * Real.pi)) + C)
        ≤ C₂ * L / T := hb3
      _ ≤ C₂ := hb4
      _ ≤ T / (32 * Real.pi ^ 2) := hb5
      _ ≤ T / (16 * Real.pi ^ 2) := hb6
      _ ≤ X := hX1
  calc |(1 / (4 * Real.pi ^ 2)) * (T * (ell1 T ^ 2 + 1 - 2 * m ^ 2))
      + (∫ τ in T..(2 * T),
          (g τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2))
      - T * ell1 T ^ 2 / (4 * Real.pi ^ 2)|
      ≤ |(1 / (4 * Real.pi ^ 2)) * (T * (ell1 T ^ 2 + 1 - 2 * m ^ 2))
          - T * ell1 T ^ 2 / (4 * Real.pi ^ 2)|
        + |∫ τ in T..(2 * T),
            (g τ ^ 2 - ((1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) ^ 2)| := htri
    _ ≤ 8 * (1 + 2 * m ^ 2) * X + 1 * X := by
        have := le_trans herrI herr_final
        linarith [hmain_dev]
    _ = (8 * (1 + 2 * m ^ 2) + 1) * (T * ell1 T ^ 2 / (4 * Real.pi ^ 2)) / L ^ 2 := by
        rw [hX]
        ring


/-- **[eq:muints].1 given Stirling**: ∫_T^{2T} g = Tℓ₁/(2π) + O(1/T)  (∃-form, from `int_g_explicit`). -/
theorem int_g_of_stirling (hcont : Continuous g)
    (hst : ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ |τ| →
      |g τ - (1 / (2 * Real.pi)) * Real.log (|τ| / (2 * Real.pi))| ≤ C / τ ^ 2) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      |(∫ τ in T..(2 * T), g τ) - T * ell1 T / (2 * Real.pi)| ≤ C / T := by
  obtain ⟨C, hC⟩ := hst
  exact ⟨C, 1, fun T hT => int_g_explicit hcont hC hT⟩

/-- **[eq:muints].2 given Stirling**: ∫_T^{2T} g² = (Tℓ₁²/4π²)(1 + O(ℓ⁻²))  (∃-form, from `int_g_sq_explicit`). -/
theorem int_g_sq_of_stirling (hcont : Continuous g)
    (hst : ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ |τ| →
      |g τ - (1 / (2 * Real.pi)) * Real.log (|τ| / (2 * Real.pi))| ≤ C / τ ^ 2) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      |(∫ τ in T..(2 * T), g τ ^ 2) - T * ell1 T ^ 2 / (4 * Real.pi ^ 2)|
        ≤ C * (T * ell1 T ^ 2 / (4 * Real.pi ^ 2)) / l T ^ 2 := by
  obtain ⟨C, hC⟩ := hst
  exact ⟨_, _, fun T hT => int_g_sq_explicit hcont hC hT⟩

end Generic

/-! ## μ_χ -/

variable {κ q : ℕ}

lemma ell1q_eq (hq : 1 ≤ q) {T : ℝ} (hT : 0 < T) : ell1q q T = ell1 T + Real.log q := by
  unfold ell1q ell1 l
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  rw [show (q : ℝ) * T / (2 * Real.pi) = q * (T / (2 * Real.pi)) by ring,
    Real.log_mul hq0.ne' (by positivity)]
  ring


/-! ## q-uniform versions for μ_χ (constants depend only on the Stirling constant) -/

/-- **q-uniform GammaFactsChiBounded.int_mu**: given the Stirling constant C (q-free), the error
constant is C and the threshold is 1, for every κ, q ≥ 1. -/
theorem int_muq_uniform (C : ℝ) : ∀ (κ q : ℕ), 1 ≤ q → Continuous (muq κ q) →
    (∀ τ : ℝ, 1 ≤ |τ| →
      |muq κ q τ - (1 / (2 * Real.pi)) * Real.log (q * |τ| / (2 * Real.pi))| ≤ C / τ ^ 2) →
    ∀ T : ℝ, 1 ≤ T →
      |(∫ τ in T..(2 * T), muq κ q τ) - T * ell1q q T / (2 * Real.pi)| ≤ C / T := by
  intro κ q hq hcont hst T hT
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hT0 : 0 < T := by linarith
  set c₀ : ℝ := Real.log q / (2 * Real.pi) with hc₀
  set g : ℝ → ℝ := fun τ => muq κ q τ - c₀ with hg
  have hgcont : Continuous g := hcont.sub continuous_const
  have hgst : ∀ τ : ℝ, 1 ≤ |τ| →
      |g τ - (1 / (2 * Real.pi)) * Real.log (|τ| / (2 * Real.pi))| ≤ C / τ ^ 2 := by
    intro τ hτ
    have hτ0 : 0 < |τ| := by linarith
    have e : g τ - (1 / (2 * Real.pi)) * Real.log (|τ| / (2 * Real.pi))
        = muq κ q τ - (1 / (2 * Real.pi)) * Real.log (q * |τ| / (2 * Real.pi)) := by
      rw [hg, hc₀]
      simp only
      rw [show (q : ℝ) * |τ| / (2 * Real.pi) = q * (|τ| / (2 * Real.pi)) by ring,
        Real.log_mul hq0.ne' (by positivity)]
      ring
    rw [e]
    exact hst τ hτ
  have hmain := int_g_explicit hgcont hgst hT
  have hgi : IntervalIntegrable g volume T (2 * T) := hgcont.intervalIntegrable _ _
  have hci : IntervalIntegrable (fun _ : ℝ => c₀) volume T (2 * T) := _root_.intervalIntegrable_const
  have hsplit : (∫ τ in T..(2 * T), muq κ q τ) = (∫ τ in T..(2 * T), g τ) + c₀ * T := by
    have e1 : (∫ τ in T..(2 * T), muq κ q τ) = ∫ τ in T..(2 * T), (g τ + c₀) := by
      apply intervalIntegral.integral_congr
      intro τ _
      rw [hg]
      ring
    rw [e1, intervalIntegral.integral_add hgi hci, intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hsplit, ell1q_eq hq hT0]
  have e2 : (∫ τ in T..(2 * T), g τ) + c₀ * T - T * (ell1 T + Real.log q) / (2 * Real.pi)
      = (∫ τ in T..(2 * T), g τ) - T * ell1 T / (2 * Real.pi) := by
    rw [hc₀]; ring
  rw [e2]
  exact hmain

set_option maxHeartbeats 800000 in
/-- **q-uniform GammaFactsChiBounded.int_mu_sq**: constants depend only on the Stirling constant C:
threshold T₀(C) := max (2π e⁴) (32π²(C(1+C)+1)) (≥ 2π e² and ≥ 1 automatically), error constant
K(C) := 8(1+2log²2)+1 + 4π·|C|. The log q of μ_χ never multiplies: 2c₀·|E₂| ≤ 2c₀C/T is absorbed by
ell1q ≥ 2π·c₀ (i.e. ell1q ≥ log q). -/
theorem int_muq_sq_uniform (C : ℝ) : ∀ (κ q : ℕ), 1 ≤ q → Continuous (muq κ q) →
    (∀ τ : ℝ, 1 ≤ |τ| →
      |muq κ q τ - (1 / (2 * Real.pi)) * Real.log (q * |τ| / (2 * Real.pi))| ≤ C / τ ^ 2) →
    ∀ T : ℝ, max (2 * Real.pi * Real.exp 4) (32 * Real.pi ^ 2 * (C * (1 + C) + 1)) ≤ T →
      |(∫ τ in T..(2 * T), muq κ q τ ^ 2) - T * ell1q q T ^ 2 / (4 * Real.pi ^ 2)|
        ≤ (8 * (1 + 2 * Real.log 2 ^ 2) + 1 + 4 * Real.pi * |C|)
          * (T * ell1q q T ^ 2 / (4 * Real.pi ^ 2)) / l T ^ 2 := by
  intro κ q hq hcont hst T hT
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  set c₀ : ℝ := Real.log q / (2 * Real.pi) with hc₀
  have hc₀0 : 0 ≤ c₀ := by rw [hc₀]; exact div_nonneg (Real.log_nonneg (by exact_mod_cast hq)) (by positivity)
  set g : ℝ → ℝ := fun τ => muq κ q τ - c₀ with hg
  have hgcont : Continuous g := hcont.sub continuous_const
  have hgst : ∀ τ : ℝ, 1 ≤ |τ| →
      |g τ - (1 / (2 * Real.pi)) * Real.log (|τ| / (2 * Real.pi))| ≤ C / τ ^ 2 := by
    intro τ hτ
    have hτ0 : 0 < |τ| := by linarith
    have e : g τ - (1 / (2 * Real.pi)) * Real.log (|τ| / (2 * Real.pi))
        = muq κ q τ - (1 / (2 * Real.pi)) * Real.log (q * |τ| / (2 * Real.pi)) := by
      rw [hg, hc₀]
      simp only
      rw [show (q : ℝ) * |τ| / (2 * Real.pi) = q * (|τ| / (2 * Real.pi)) by ring,
        Real.log_mul hq0.ne' (by positivity)]
      ring
    rw [e]
    exact hst τ hτ
  have hC0 : 0 ≤ C := by
    have h := hst 1 (by norm_num)
    have := abs_nonneg (muq κ q 1 - 1 / (2 * Real.pi) * Real.log (q * |1| / (2 * Real.pi)))
    nlinarith
  -- thresholds
  have hTe4 : 2 * Real.pi * Real.exp 4 ≤ T := le_trans (le_max_left _ _) hT
  have hexp1 : (1 : ℝ) ≤ Real.exp 4 := by have := Real.add_one_le_exp (4 : ℝ); linarith
  have hT0 : (0 : ℝ) < T := by nlinarith [Real.exp_pos (4 : ℝ), Real.pi_gt_three]
  have hT1 : (1 : ℝ) ≤ T := by nlinarith [Real.pi_gt_three]
  have hl2 : (2 : ℝ) ≤ l T := by
    have h1 : Real.exp 4 ≤ T / (2 * Real.pi) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    have h2 := Real.log_le_log (Real.exp_pos 4) h1
    rw [Real.log_exp] at h2
    unfold l
    linarith
  have hm : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hell1 : (1 : ℝ) ≤ ell1 T := by unfold ell1; nlinarith
  have hellq : ell1q q T = ell1 T + Real.log q := ell1q_eq hq hT0
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have hell_le : ell1 T ≤ ell1q q T := by rw [hellq]; linarith
  have hellq1 : (1 : ℝ) ≤ ell1q q T := le_trans hell1 hell_le
  have hellq_c₀ : 2 * Real.pi * c₀ ≤ ell1q q T := by
    rw [hellq, hc₀]; field_simp; linarith
  -- sizes
  set X : ℝ := T * ell1 T ^ 2 / (4 * Real.pi ^ 2) with hX
  set Xq : ℝ := T * ell1q q T ^ 2 / (4 * Real.pi ^ 2) with hXq
  have hX0 : 0 ≤ X := by positivity
  have hXle : X ≤ Xq := by
    rw [hX, hXq]
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ hT0.le
    nlinarith
  have hlpos : 0 < l T := by linarith
  have hl2' : 0 < l T ^ 2 := by positivity
  have hlT : l T ≤ T := by
    unfold l
    have h1 := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < T / (2 * Real.pi))
    have h2 : T / (2 * Real.pi) ≤ T := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [Real.pi_gt_three]
    linarith
  -- the c₀-free key: 2c₀ · (C/T) ≤ 4π·C · Xq / l²
  have hkey : 2 * c₀ * (C / T) ≤ (4 * Real.pi * C) * Xq / l T ^ 2 := by
    rw [hXq]
    rw [show 2 * c₀ * (C / T) = (2 * c₀ * C) / T by ring, div_le_div_iff₀ hT0 hl2']
    -- 2c₀C·l² ≤ 4πC·(T ell1q²/(4π²))·T
    have e : (4 * Real.pi * C) * (T * ell1q q T ^ 2 / (4 * Real.pi ^ 2)) * T
        = (C / Real.pi) * (T ^ 2 * ell1q q T ^ 2) := by field_simp
    rw [e]
    -- ell1q² ≥ (2π c₀)·1
    have h1 : 2 * Real.pi * c₀ ≤ ell1q q T ^ 2 := by nlinarith [hellq_c₀, hellq1]
    have h2 : l T ^ 2 ≤ T ^ 2 := by nlinarith
    -- 2 c₀ C l² ≤ (C/π)·T²·(2π c₀) = 2 c₀ C T²  ≤ (C/π) T² ell1q²
    have h3 : 2 * c₀ * C * l T ^ 2 ≤ 2 * c₀ * C * T ^ 2 := by
      apply mul_le_mul_of_nonneg_left h2; positivity
    have h4 : 2 * c₀ * C * T ^ 2 = (C / Real.pi) * (T ^ 2 * (2 * Real.pi * c₀)) := by field_simp
    have h5 : (C / Real.pi) * (T ^ 2 * (2 * Real.pi * c₀)) ≤ (C / Real.pi) * (T ^ 2 * ell1q q T ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  -- generic estimates with explicit constants
  have E₁ := int_g_sq_explicit hgcont hgst hT
  have E₂ := int_g_explicit hgcont hgst hT1
  -- decomposition
  have hgi : IntervalIntegrable g volume T (2 * T) := hgcont.intervalIntegrable _ _
  have hg2i : IntervalIntegrable (fun τ => g τ ^ 2) volume T (2 * T) :=
    (hgcont.pow 2).intervalIntegrable _ _
  have hli : IntervalIntegrable (fun τ => (2 * c₀) * g τ) volume T (2 * T) := hgi.const_mul _
  have hci : IntervalIntegrable (fun _ : ℝ => c₀ ^ 2) volume T (2 * T) :=
    _root_.intervalIntegrable_const
  have hsplit : (∫ τ in T..(2 * T), muq κ q τ ^ 2)
      = (∫ τ in T..(2 * T), g τ ^ 2) + 2 * c₀ * (∫ τ in T..(2 * T), g τ) + c₀ ^ 2 * T := by
    have e1 : (∫ τ in T..(2 * T), muq κ q τ ^ 2)
        = ∫ τ in T..(2 * T), (g τ ^ 2 + ((2 * c₀) * g τ + c₀ ^ 2)) := by
      apply intervalIntegral.integral_congr
      intro τ _
      rw [hg]
      ring
    rw [e1, intervalIntegral.integral_add hg2i (hli.add hci), intervalIntegral.integral_add hli hci,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const, smul_eq_mul]
    ring
  have htarget : Xq = X + 2 * c₀ * (T * ell1 T / (2 * Real.pi)) + c₀ ^ 2 * T := by
    rw [hXq, hX, hellq, hc₀]; field_simp; ring
  rw [hsplit]
  have ediff : (∫ τ in T..(2 * T), g τ ^ 2) + 2 * c₀ * (∫ τ in T..(2 * T), g τ) + c₀ ^ 2 * T - Xq
      = ((∫ τ in T..(2 * T), g τ ^ 2) - X)
        + 2 * c₀ * ((∫ τ in T..(2 * T), g τ) - T * ell1 T / (2 * Real.pi)) := by
    rw [htarget]; ring
  rw [ediff]
  set K₁ : ℝ := 8 * (1 + 2 * Real.log 2 ^ 2) + 1 with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  have b1 : |(∫ τ in T..(2 * T), g τ ^ 2) - X| ≤ K₁ * Xq / l T ^ 2 := by
    calc |(∫ τ in T..(2 * T), g τ ^ 2) - X| ≤ K₁ * X / l T ^ 2 := E₁
      _ ≤ K₁ * Xq / l T ^ 2 := by
          apply div_le_div_of_nonneg_right _ hl2'.le
          exact mul_le_mul_of_nonneg_left hXle hK₁0
  have b2 : |2 * c₀ * ((∫ τ in T..(2 * T), g τ) - T * ell1 T / (2 * Real.pi))|
      ≤ (4 * Real.pi * C) * Xq / l T ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * c₀)]
    calc 2 * c₀ * |(∫ τ in T..(2 * T), g τ) - T * ell1 T / (2 * Real.pi)|
        ≤ 2 * c₀ * (C / T) := mul_le_mul_of_nonneg_left E₂ (by positivity)
      _ ≤ (4 * Real.pi * C) * Xq / l T ^ 2 := hkey
  have hCabs : 4 * Real.pi * C ≤ 4 * Real.pi * |C| := by
    apply mul_le_mul_of_nonneg_left (le_abs_self C); positivity
  have hXq0 : 0 ≤ Xq / l T ^ 2 := by positivity
  calc |((∫ τ in T..(2 * T), g τ ^ 2) - X)
        + 2 * c₀ * ((∫ τ in T..(2 * T), g τ) - T * ell1 T / (2 * Real.pi))|
      ≤ |(∫ τ in T..(2 * T), g τ ^ 2) - X|
        + |2 * c₀ * ((∫ τ in T..(2 * T), g τ) - T * ell1 T / (2 * Real.pi))| := abs_add_le _ _
    _ ≤ K₁ * Xq / l T ^ 2 + (4 * Real.pi * C) * Xq / l T ^ 2 := add_le_add b1 b2
    _ = (K₁ + 4 * Real.pi * C) * (Xq / l T ^ 2) := by ring
    _ ≤ (K₁ + 4 * Real.pi * |C|) * (Xq / l T ^ 2) := by
        apply mul_le_mul_of_nonneg_right _ hXq0; linarith
    _ = (K₁ + 4 * Real.pi * |C|) * Xq / l T ^ 2 := by ring


/-! ## μ_χ at fixed q (∃-forms, from the q-uniform versions) -/

/-- **GammaFactsChi.int_mu** from continuity + the Stirling field of μ_χ. -/
theorem int_muq_of_stirling (hq : 1 ≤ q) (hcont : Continuous (muq κ q))
    (hst : ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ |τ| →
      |muq κ q τ - (1 / (2 * Real.pi)) * Real.log (q * |τ| / (2 * Real.pi))| ≤ C / τ ^ 2) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      |(∫ τ in T..(2 * T), muq κ q τ) - T * ell1q q T / (2 * Real.pi)| ≤ C / T := by
  obtain ⟨C, hC⟩ := hst
  exact ⟨C, 1, fun T hT => int_muq_uniform C κ q hq hcont hC T hT⟩

/-- **GammaFactsChi.int_mu_sq** from continuity + the Stirling field of μ_χ. -/
theorem int_muq_sq_of_stirling (hq : 1 ≤ q) (hcont : Continuous (muq κ q))
    (hst : ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ |τ| →
      |muq κ q τ - (1 / (2 * Real.pi)) * Real.log (q * |τ| / (2 * Real.pi))| ≤ C / τ ^ 2) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      |(∫ τ in T..(2 * T), muq κ q τ ^ 2) - T * ell1q q T ^ 2 / (4 * Real.pi ^ 2)|
        ≤ C * (T * ell1q q T ^ 2 / (4 * Real.pi ^ 2)) / l T ^ 2 := by
  obtain ⟨C, hC⟩ := hst
  exact ⟨_, _, fun T hT => int_muq_sq_uniform C κ q hq hcont hC T hT⟩

end IntMuChi
end ThmE
end Zeta23
