/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Chebyshev.lean — discharge of the Chebyshev-type hypothesis H-cheb.

Paper: "More than two thirds of the zeros of the Riemann zeta function lie on
the critical line", Lemma [lem:cheb], displays [eq:cheb1]–[eq:cheb2]:

  "For x ≥ 2,
     Σ_{n≤x} Λ(n) ≪ x,   Σ_{n≤x} Λ(n)/√n ≤ 3√x  (x ≥ x₀),
     Σ_{n≤x} Λ(n)/(√n log n) ≪ √x/log x,   Σ_{n≤x} Λ(n)² ≪ x log x,    [eq:cheb1]
     Σ_{n≤x} Λ(n)²/n = (log x)²/2 + O(log x),
     Σ_{n≤x} Λ(n)²/n (log x − log n) = (log x)³/6 + O((log x)²).       [eq:cheb2]"

H-cheb is classical [MV07 §2.2].  All sums here run over n ∈ Finset.Ioc 0 ⌊x⌋₊,
matching Mathlib's `Chebyshev.psi`.  The ≪-bounds are stated with explicit
existential constants; the paper's "≤ 3√x eventually" is provided in the robust
∃-constant form (the constant is not load-bearing downstream — [eq:Bdef] only
needs *some* B = l + C√X).

The two [eq:cheb2] asymptotics need Mertens' first theorem
Σ_{n≤x} Λ(n)/n = log x + O(1), which is not in Mathlib; it is supplied by
`mertensFirst` below, via Zeta23/FromPNTPlus/Mertens.lean.

Everything else comes from Mathlib (NumberTheory.Chebyshev ψ-bounds +
elementary induction/splitting arguments).
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Zeta23.FromPNTPlus.Mertens
import Zeta23.Hypotheses

namespace Zeta23
namespace Cheb

open Finset Real Chebyshev
open ArithmeticFunction hiding log
open scoped Nat.Prime

/-! ## [eq:cheb1], first bound: Σ_{n≤x} Λ(n) ≪ x -/

/-- [eq:cheb1].1: Σ_{n≤x} Λ(n) ≪ x, with Mathlib's explicit Chebyshev constant. -/
theorem sum_vonMangoldt_le {x : ℝ} (hx : 0 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ≤ (Real.log 4 + 4) * x :=
  Chebyshev.psi_le_const_mul_self hx

/-! ## [eq:cheb1], second bound: Σ_{n≤x} Λ(n)/√n ≪ √x -/


section Cheb1b

open MeasureTheory intervalIntegral

private lemma sum_Icc_eq_sum_Ioc {c : ℕ → ℝ} (hc : c 0 = 0) (n : ℕ) :
    ∑ k ∈ Icc 0 n, c k = ∑ k ∈ Ioc 0 n, c k := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le n), Finset.sum_cons, hc, zero_add]

private lemma psi_eq_sum_Icc' (t : ℝ) :
    ∑ k ∈ Icc 0 ⌊t⌋₊, Λ k = Chebyshev.psi t := by
  rw [sum_Icc_eq_sum_Ioc (by simp) ⌊t⌋₊]; rfl

/-- Abel summation specialised to Σ_{n≤x} Λ(n)/√n, in terms of ψ. -/
private lemma abel_sqrt {x : ℝ} (_hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / Real.sqrt n
      = x ^ (-(2⁻¹ : ℝ)) * Chebyshev.psi x
        + 2⁻¹ * ∫ t in Set.Ioc 1 x, t ^ (-(2⁻¹ : ℝ) - 1) * Chebyshev.psi t := by
  have hf_diff : ∀ t ∈ Set.Icc (1 : ℝ) x,
      DifferentiableAt ℝ (fun t : ℝ => t ^ (-(2⁻¹ : ℝ))) t := fun t ht =>
    Real.differentiableAt_rpow_const_of_ne _ (by nlinarith [ht.1] : t ≠ 0)
  have hderiv : deriv (fun t : ℝ => t ^ (-(2⁻¹ : ℝ)))
      = fun t : ℝ => -(2⁻¹ : ℝ) * t ^ (-(2⁻¹ : ℝ) - 1) := Real.deriv_rpow_const' _
  have hf_int : IntegrableOn (deriv fun t : ℝ => t ^ (-(2⁻¹ : ℝ))) (Set.Icc 1 x) := by
    rw [hderiv]
    refine (ContinuousOn.mul continuousOn_const ?_).integrableOn_Icc
    intro t ht
    exact (Real.continuousAt_rpow_const t _
      (Or.inl (by nlinarith [ht.1] : t ≠ 0))).continuousWithinAt
  have habel := sum_mul_eq_sub_integral_mul₀ (fun n => Λ n) (by simp) x hf_diff hf_int
  have hL : ∑ k ∈ Icc 0 ⌊x⌋₊, (k : ℝ) ^ (-(2⁻¹ : ℝ)) * Λ k
      = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / Real.sqrt n := by
    rw [sum_Icc_eq_sum_Ioc (by simp) ⌊x⌋₊]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hrw : (k : ℝ) ^ (-(2⁻¹ : ℝ)) = (Real.sqrt k)⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (Nat.cast_nonneg k)]
      norm_num
    rw [hrw, div_eq_mul_inv, mul_comm]
  rw [hL, psi_eq_sum_Icc'] at habel
  have hI : (∫ t in Set.Ioc 1 x, deriv (fun t : ℝ => t ^ (-(2⁻¹ : ℝ))) t
        * ∑ k ∈ Icc 0 ⌊t⌋₊, (fun n => Λ n) k)
      = -(2⁻¹ : ℝ) * ∫ t in Set.Ioc 1 x, t ^ (-(2⁻¹ : ℝ) - 1) * Chebyshev.psi t := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
    simp only [hderiv]
    rw [← psi_eq_sum_Icc' t]
    ring
  rw [habel, hI]
  ring

/-- The tail integral bound: ∫₁ˣ t^{-3/2} ψ(t) dt ≤ log 4·(2√x − 2) + (log x)². -/
private lemma integral_tail_bound {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in Set.Ioc 1 x, t ^ (-(2⁻¹ : ℝ) - 1) * Chebyshev.psi t
      ≤ Real.log 4 * (2 * Real.sqrt x - 2) + Real.log x ^ 2 := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  -- the explicit dominating integrand
  set g : ℝ → ℝ := fun t => Real.log 4 * t ^ (-(2⁻¹ : ℝ)) + 2 * (Real.log t * t⁻¹) with hg
  have hcont_g : ContinuousOn g (Set.Icc 1 x) := by
    apply ContinuousOn.add
    · exact continuousOn_const.mul fun t ht =>
        (Real.continuousAt_rpow_const t _
          (Or.inl (by nlinarith [ht.1] : t ≠ 0))).continuousWithinAt
    · refine continuousOn_const.mul (ContinuousOn.mul ?_ ?_)
      · exact fun t ht => (Real.continuousAt_log (by nlinarith [ht.1])).continuousWithinAt
      · exact continuousOn_inv₀.mono fun t ht => by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          nlinarith [ht.1]
  -- step 1: pointwise comparison with g on Ioc 1 x
  have hpoint : ∀ t ∈ Set.Ioc (1 : ℝ) x,
      t ^ (-(2⁻¹ : ℝ) - 1) * Chebyshev.psi t ≤ g t := by
    intro t ht
    have ht1 : (1 : ℝ) ≤ t := ht.1.le
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
    have hψ : Chebyshev.psi t ≤ Real.log 4 * t + 2 * Real.sqrt t * Real.log t :=
      Chebyshev.psi_le ht1
    have hrnn : (0 : ℝ) ≤ t ^ (-(2⁻¹ : ℝ) - 1) := Real.rpow_nonneg ht0.le _
    calc t ^ (-(2⁻¹ : ℝ) - 1) * Chebyshev.psi t
        ≤ t ^ (-(2⁻¹ : ℝ) - 1) * (Real.log 4 * t + 2 * Real.sqrt t * Real.log t) :=
          mul_le_mul_of_nonneg_left hψ hrnn
      _ = g t := by
          rw [hg]
          have e1 : t ^ (-(2⁻¹ : ℝ) - 1) * t = t ^ (-(2⁻¹ : ℝ)) := by
            rw [← Real.rpow_add_one ht0.ne']
            ring_nf
          have e2 : t ^ (-(2⁻¹ : ℝ) - 1) * Real.sqrt t = t⁻¹ := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht0, ← Real.rpow_neg_one t]
            norm_num
          calc t ^ (-(2⁻¹ : ℝ) - 1) * (Real.log 4 * t + 2 * Real.sqrt t * Real.log t)
              = Real.log 4 * (t ^ (-(2⁻¹ : ℝ) - 1) * t)
                + 2 * ((t ^ (-(2⁻¹ : ℝ) - 1) * Real.sqrt t) * Real.log t) := by ring
            _ = Real.log 4 * t ^ (-(2⁻¹ : ℝ)) + 2 * (Real.log t * t⁻¹) := by
                rw [e1, e2]; ring
  -- step 2: integrability of both sides on Ioc 1 x
  have hint_g : IntegrableOn g (Set.Ioc 1 x) :=
    (hcont_g.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hmeas_f : AEStronglyMeasurable (fun t : ℝ => t ^ (-(2⁻¹ : ℝ) - 1) * Chebyshev.psi t)
      (volume.restrict (Set.Ioc 1 x)) := by
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (ContinuousOn.aestronglyMeasurable (fun t ht =>
        (Real.continuousAt_rpow_const t _
          (Or.inl (by nlinarith [(Set.mem_Ioc.mp ht).1] : t ≠ 0))).continuousWithinAt)
        measurableSet_Ioc)
    · exact (Chebyshev.psi_mono.measurable.aestronglyMeasurable).restrict
  have hint_f : IntegrableOn (fun t : ℝ => t ^ (-(2⁻¹ : ℝ) - 1) * Chebyshev.psi t)
      (Set.Ioc 1 x) := by
    refine Integrable.mono' (g := fun _ => (Real.log 4 + 4) * x)
      (integrableOn_const (by simp)) hmeas_f ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht1 : (1 : ℝ) ≤ t := ht.1.le
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
    have h1 : t ^ (-(2⁻¹ : ℝ) - 1) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos ht1 (by norm_num)
    have h2 : (0 : ℝ) ≤ Chebyshev.psi t := Chebyshev.psi_nonneg t
    have h3 : Chebyshev.psi t ≤ (Real.log 4 + 4) * x :=
      le_trans (Chebyshev.psi_mono ht.2) (Chebyshev.psi_le_const_mul_self hx0.le)
    have hrnn : (0 : ℝ) ≤ t ^ (-(2⁻¹ : ℝ) - 1) := Real.rpow_nonneg ht0.le _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hrnn h2)]
    calc t ^ (-(2⁻¹ : ℝ) - 1) * Chebyshev.psi t ≤ 1 * Chebyshev.psi t :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = Chebyshev.psi t := one_mul _
      _ ≤ (Real.log 4 + 4) * x := h3
  -- step 3: compare, then evaluate ∫ g
  refine le_trans (setIntegral_mono_on hint_f hint_g measurableSet_Ioc hpoint) ?_
  rw [← intervalIntegral.integral_of_le hx]
  have hi1 : IntervalIntegrable (fun t : ℝ => Real.log 4 * t ^ (-(2⁻¹ : ℝ))) volume 1 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    exact continuousOn_const.mul fun t ht =>
      (Real.continuousAt_rpow_const t _
        (Or.inl (by nlinarith [ht.1] : t ≠ 0))).continuousWithinAt
  have hi2 : IntervalIntegrable (fun t : ℝ => 2 * (Real.log t * t⁻¹)) volume 1 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    refine continuousOn_const.mul (ContinuousOn.mul ?_ ?_)
    · exact fun t ht => (Real.continuousAt_log (by nlinarith [ht.1])).continuousWithinAt
    · exact continuousOn_inv₀.mono fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        nlinarith [ht.1]
  rw [hg]
  rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  have hv1 : ∫ t in (1:ℝ)..x, t ^ (-(2⁻¹ : ℝ)) = 2 * Real.sqrt x - 2 := by
    rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(2⁻¹)))]
    rw [Real.one_rpow]
    rw [Real.sqrt_eq_rpow]
    norm_num
    ring
  have hv2 : ∫ t in (1:ℝ)..x, Real.log t * t⁻¹ = Real.log x ^ 2 / 2 := by
    have hftc : ∀ t ∈ Set.uIcc (1:ℝ) x,
        HasDerivAt (fun t : ℝ => Real.log t ^ 2 / 2) (Real.log t * t⁻¹) t := by
      intro t ht
      rw [Set.uIcc_of_le hx] at ht
      have ht0 : t ≠ 0 := by nlinarith [ht.1]
      have h := ((Real.hasDerivAt_log ht0).pow 2).div_const 2
      have heq : Real.log t * t⁻¹ = ((2 : ℕ) : ℝ) * Real.log t ^ (2 - 1) * t⁻¹ / 2 := by
        push_cast
        ring
      rw [heq]
      exact h
    have hint : IntervalIntegrable (fun t : ℝ => Real.log t * t⁻¹) volume 1 x := by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le hx]
      refine ContinuousOn.mul ?_ ?_
      · exact fun t ht => (Real.continuousAt_log (by nlinarith [ht.1])).continuousWithinAt
      · exact continuousOn_inv₀.mono fun t ht => by
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          nlinarith [ht.1]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hftc hint]
    simp [Real.log_one]
  rw [hv1, hv2]
  ring_nf
  nlinarith [Real.sqrt_nonneg x, Real.log_nonneg hx]

end Cheb1b

/-- Precise partial-summation bound: Σ_{n≤x} Λ(n)/√n ≤ 2 log 4·√x + 2 log x + (log x)²/2. -/
theorem sum_vonMangoldt_div_sqrt_le_precise {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / Real.sqrt n
      ≤ 2 * Real.log 4 * Real.sqrt x + 2 * Real.log x + Real.log x ^ 2 / 2 := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  rw [abel_sqrt hx]
  have h1 : x ^ (-(2⁻¹ : ℝ)) * Chebyshev.psi x
      ≤ Real.log 4 * Real.sqrt x + 2 * Real.log x := by
    have hψ := Chebyshev.psi_le hx
    have hnn : (0 : ℝ) ≤ x ^ (-(2⁻¹ : ℝ)) := Real.rpow_nonneg hx0.le _
    have e1 : x ^ (-(2⁻¹ : ℝ)) * x = Real.sqrt x := by
      rw [← Real.rpow_add_one hx0.ne', Real.sqrt_eq_rpow]; norm_num
    have e2 : x ^ (-(2⁻¹ : ℝ)) * Real.sqrt x = 1 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx0]; norm_num
    calc x ^ (-(2⁻¹ : ℝ)) * Chebyshev.psi x
        ≤ x ^ (-(2⁻¹ : ℝ)) * (Real.log 4 * x + 2 * Real.sqrt x * Real.log x) :=
          mul_le_mul_of_nonneg_left hψ hnn
      _ = Real.log 4 * (x ^ (-(2⁻¹ : ℝ)) * x)
          + 2 * (x ^ (-(2⁻¹ : ℝ)) * Real.sqrt x) * Real.log x := by ring
      _ = Real.log 4 * Real.sqrt x + 2 * Real.log x := by rw [e1, e2]; ring
  have h2 := integral_tail_bound hx
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  nlinarith [h1, h2]

/-- [eq:cheb1].2, all-x form: Σ_{n≤x} Λ(n)/√n ≤ (2 log 4 + 16)·√x for x ≥ 1. -/
theorem sum_vonMangoldt_div_sqrt_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / Real.sqrt n ≤ (2 * Real.log 4 + 16) * Real.sqrt x := by
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx
  have h := sum_vonMangoldt_div_sqrt_le_precise hx
  have hq : x ^ ((4 : ℝ)⁻¹) * x ^ ((4 : ℝ)⁻¹) = Real.sqrt x := by
    rw [← Real.rpow_add hx0, Real.sqrt_eq_rpow]; norm_num
  have hlog : Real.log x ≤ 4 * x ^ ((4 : ℝ)⁻¹) := by
    have h4 := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 4⁻¹)
    rw [div_eq_mul_inv, inv_inv] at h4
    linarith
  have h14 : x ^ ((4 : ℝ)⁻¹) ≤ Real.sqrt x := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hlognn : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
  have h14nn : (0 : ℝ) ≤ x ^ ((4 : ℝ)⁻¹) := Real.rpow_nonneg hx0.le _
  have hsq : Real.log x ^ 2 ≤ 16 * Real.sqrt x := by nlinarith [hlog, hlognn, hq, h14nn]
  have h2log : 2 * Real.log x ≤ 8 * Real.sqrt x := by nlinarith [hlog, h14, h14nn]
  nlinarith [h, hsq, h2log]

/-- [eq:cheb1].2 with the threshold explicit (effective version): the witness of
`sum_vonMangoldt_div_sqrt_le_three` is `x₀ = max 1 ((48/(3 − 2 log 4))⁴)` (≤ 2.0·10⁹). -/
theorem sum_vonMangoldt_div_sqrt_le_three_explicit {x : ℝ}
    (hx : max 1 ((48 / (3 - 2 * Real.log 4)) ^ 4) ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / Real.sqrt n ≤ 3 * Real.sqrt x := by
  have hlog4lt : Real.log 4 < 3 / 2 := by
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    rw [h2]; nlinarith [Real.log_two_lt_d9]
  set c : ℝ := 3 - 2 * Real.log 4 with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  have hx' : max 1 ((48 / c) ^ 4) ≤ x := by rw [hc]; exact hx

  have hx1 : (1 : ℝ) ≤ x := le_trans (le_max_left _ _) hx'
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  have h := sum_vonMangoldt_div_sqrt_le_precise hx1
  have hlog8 : Real.log x ≤ 8 * x ^ ((8 : ℝ)⁻¹) := by
    have h8 := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 8⁻¹)
    rw [div_eq_mul_inv, inv_inv] at h8
    linarith
  have h18nn : (0 : ℝ) ≤ x ^ ((8 : ℝ)⁻¹) := Real.rpow_nonneg hx0.le _
  have h14nn : (0 : ℝ) ≤ x ^ ((4 : ℝ)⁻¹) := Real.rpow_nonneg hx0.le _
  have hq8 : x ^ ((8 : ℝ)⁻¹) * x ^ ((8 : ℝ)⁻¹) = x ^ ((4 : ℝ)⁻¹) := by
    rw [← Real.rpow_add hx0]; norm_num
  have hsq : Real.log x ^ 2 ≤ 64 * x ^ ((4 : ℝ)⁻¹) := by
    nlinarith [hlog8, Real.log_nonneg hx1, hq8, h18nn]
  have h84 : x ^ ((8 : ℝ)⁻¹) ≤ x ^ ((4 : ℝ)⁻¹) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hbound : 2 * Real.log x + Real.log x ^ 2 / 2 ≤ 48 * x ^ ((4 : ℝ)⁻¹) := by
    nlinarith [hlog8, hsq, h84]
  have hxc : (48 / c) ^ 4 ≤ x := le_trans (le_max_right _ _) hx'
  have h48nn : (0 : ℝ) ≤ 48 / c := by positivity
  have hx14 : 48 / c ≤ x ^ ((4 : ℝ)⁻¹) := by
    have hmono := Real.rpow_le_rpow (by positivity) hxc (by norm_num : (0 : ℝ) ≤ 4⁻¹)
    rwa [← Real.rpow_natCast (48 / c) 4, ← Real.rpow_mul h48nn,
      (by norm_num : ((4 : ℕ) : ℝ) * (4 : ℝ)⁻¹ = 1), Real.rpow_one] at hmono
  have hsqrt : Real.sqrt x = x ^ ((4 : ℝ)⁻¹) * x ^ ((4 : ℝ)⁻¹) := by
    rw [← Real.rpow_add hx0, Real.sqrt_eq_rpow]; norm_num
  have hkey : 48 * x ^ ((4 : ℝ)⁻¹) ≤ c * Real.sqrt x := by
    rw [hsqrt]
    have hc48 : c * (48 / c) = 48 := by field_simp
    have h1 : (48 : ℝ) ≤ c * x ^ ((4 : ℝ)⁻¹) := by
      have h2 := mul_le_mul_of_nonneg_left hx14 hcpos.le
      rwa [hc48] at h2
    calc 48 * x ^ ((4 : ℝ)⁻¹) ≤ (c * x ^ ((4 : ℝ)⁻¹)) * x ^ ((4 : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_right h1 h14nn
      _ = c * (x ^ ((4 : ℝ)⁻¹) * x ^ ((4 : ℝ)⁻¹)) := by ring
  nlinarith [h, hbound, hkey, hc]

/-- [eq:cheb1].2, the paper's literal form (∃-version; witness = the explicit threshold above). -/
theorem sum_vonMangoldt_div_sqrt_le_three :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / Real.sqrt n ≤ 3 * Real.sqrt x :=
  ⟨max 1 ((48 / (3 - 2 * Real.log 4)) ^ 4), fun _ hx => sum_vonMangoldt_div_sqrt_le_three_explicit hx⟩

/-! ## [eq:cheb1], third bound: Σ_{n≤x} Λ(n)/(√n log n) ≪ √x/log x -/

/-- Σ_{n≤N} 1/√n ≤ 2√N (elementary induction). -/
theorem sum_one_div_sqrt_le (N : ℕ) :
    ∑ n ∈ Ioc 0 N, (1 : ℝ) / Real.sqrt n ≤ 2 * Real.sqrt N := by
  induction N with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le m)]
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hs : (0 : ℝ) < Real.sqrt ((m : ℝ) + 1) := Real.sqrt_pos.mpr hm1
    have h1 : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) := Real.sq_sqrt (Nat.cast_nonneg m)
    have h2 : Real.sqrt ((m : ℝ) + 1) ^ 2 = (m : ℝ) + 1 := Real.sq_sqrt hm1.le
    have key : 1 / Real.sqrt ((m : ℝ) + 1) ≤
        2 * Real.sqrt ((m : ℝ) + 1) - 2 * Real.sqrt (m : ℝ) := by
      rw [div_le_iff₀ hs]
      nlinarith [sq_nonneg (Real.sqrt ((m : ℝ) + 1) - Real.sqrt (m : ℝ)),
        Real.sqrt_nonneg (m : ℝ), Real.sqrt_nonneg ((m : ℝ) + 1)]
    have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    linarith [ih, key]

/-- [eq:cheb1].3: Σ_{n≤x} Λ(n)/(√n log n) ≤ C·√x/log x for x ≥ 2.
(The n = 1 summand is 0 in Lean: Λ 1 = 0.) -/
theorem sum_vonMangoldt_div_sqrt_mul_log_le {x : ℝ} (hx : 2 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (Real.sqrt n * Real.log n) ≤
      (4 * Real.log 4 + 40) * Real.sqrt x / Real.log x := by
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hlx : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  set R : ℕ := ⌊Real.sqrt x⌋₊ with hR
  have hsqx : Real.sqrt x ≤ x := (Real.sqrt_le_left hx0.le).mpr (by nlinarith)
  have hRle : R ≤ ⌊x⌋₊ := Nat.floor_le_floor hsqx
  have hsplit : (∑ n ∈ Ioc 0 R, Λ n / (Real.sqrt n * Real.log n))
      + ∑ n ∈ Ioc R ⌊x⌋₊, Λ n / (Real.sqrt n * Real.log n)
      = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (Real.sqrt n * Real.log n) :=
    Finset.sum_Ioc_consecutive _ (Nat.zero_le R) hRle
  rw [← hsplit]
  -- part 1: n ≤ R = ⌊√x⌋
  have hpart1 : ∑ n ∈ Ioc 0 R, Λ n / (Real.sqrt n * Real.log n)
      ≤ 2 * Real.sqrt R := by
    refine le_trans (Finset.sum_le_sum fun n hn => ?_) (sum_one_div_sqrt_le R)
    obtain ⟨hn0, _⟩ := Finset.mem_Ioc.mp hn
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · have hn1 : n = 1 := by omega
      subst hn1
      simp [vonMangoldt_apply_one]
    · have hncast : (1 : ℝ) < (n : ℝ) := by exact_mod_cast h2.trans_lt' one_lt_two
      have hlogn : (0 : ℝ) < Real.log n := Real.log_pos hncast
      have hsn : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by positivity)
      calc Λ n / (Real.sqrt n * Real.log n)
          ≤ Real.log n / (Real.sqrt n * Real.log n) := by
            gcongr
            exact vonMangoldt_le_log
        _ = 1 / Real.sqrt n := by field_simp
  have hq : x ^ ((4 : ℝ)⁻¹) * x ^ ((4 : ℝ)⁻¹) = Real.sqrt x := by
    rw [← Real.rpow_add hx0, Real.sqrt_eq_rpow]; norm_num
  have h14nn : (0 : ℝ) ≤ x ^ ((4 : ℝ)⁻¹) := Real.rpow_nonneg hx0.le _
  have hsqR : Real.sqrt R ≤ x ^ ((4 : ℝ)⁻¹) := by
    have h1 : Real.sqrt (R : ℝ) ≤ Real.sqrt (Real.sqrt x) :=
      Real.sqrt_le_sqrt (Nat.floor_le (Real.sqrt_nonneg x))
    have h2 : Real.sqrt (Real.sqrt x) = x ^ ((4 : ℝ)⁻¹) := by
      rw [Real.sqrt_eq_rpow (Real.sqrt x), Real.sqrt_eq_rpow x, ← Real.rpow_mul hx0.le]
      norm_num
    rwa [h2] at h1
  have hlog : Real.log x ≤ 4 * x ^ ((4 : ℝ)⁻¹) := by
    have h4 := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 4⁻¹)
    rw [div_eq_mul_inv, inv_inv] at h4
    linarith
  -- part 2: √x < n ≤ x
  have hS := sum_vonMangoldt_div_sqrt_le hx1
  have hsub : ∑ n ∈ Ioc R ⌊x⌋₊, Λ n / Real.sqrt n
      ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / Real.sqrt n := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ => ?_
    · exact Finset.Ioc_subset_Ioc (Nat.zero_le R) le_rfl
    · exact div_nonneg vonMangoldt_nonneg (Real.sqrt_nonneg _)
  have hpart2 : ∑ n ∈ Ioc R ⌊x⌋₊, Λ n / (Real.sqrt n * Real.log n)
      ≤ 2 / Real.log x * ((2 * Real.log 4 + 16) * Real.sqrt x) := by
    have step : ∀ n ∈ Ioc R ⌊x⌋₊, Λ n / (Real.sqrt n * Real.log n)
        ≤ 2 / Real.log x * (Λ n / Real.sqrt n) := by
      intro n hn
      obtain ⟨hnR, _⟩ := Finset.mem_Ioc.mp hn
      have hsx : Real.sqrt x < (n : ℝ) := by
        have := Nat.lt_floor_add_one (Real.sqrt x)
        have hn1 : (R : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hnR
        rw [hR] at hn1
        linarith
      have hsx0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
      have hn0 : (0 : ℝ) < (n : ℝ) := lt_trans hsx0 hsx
      have hlogn : Real.log x / 2 ≤ Real.log n := by
        have := Real.log_le_log hsx0 hsx.le
        rwa [Real.log_sqrt hx0.le] at this
      have hlogn0 : (0 : ℝ) < Real.log n := lt_of_lt_of_le (by positivity) hlogn
      have hsn : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hn0
      have hΛ : (0 : ℝ) ≤ Λ n := vonMangoldt_nonneg
      have ha : (0 : ℝ) ≤ Λ n / Real.sqrt n := div_nonneg hΛ hsn.le
      have hL2 : (0 : ℝ) < Real.log x / 2 := by positivity
      calc Λ n / (Real.sqrt n * Real.log n)
          = (Λ n / Real.sqrt n) / Real.log n := by rw [div_div]
        _ ≤ (Λ n / Real.sqrt n) / (Real.log x / 2) := by
            rw [div_le_div_iff₀ hlogn0 hL2]
            exact mul_le_mul_of_nonneg_left hlogn ha
        _ = 2 / Real.log x * (Λ n / Real.sqrt n) := by
            rw [div_div_eq_mul_div]
            ring
    calc ∑ n ∈ Ioc R ⌊x⌋₊, Λ n / (Real.sqrt n * Real.log n)
        ≤ ∑ n ∈ Ioc R ⌊x⌋₊, 2 / Real.log x * (Λ n / Real.sqrt n) :=
          Finset.sum_le_sum step
      _ = 2 / Real.log x * ∑ n ∈ Ioc R ⌊x⌋₊, Λ n / Real.sqrt n := by
          rw [Finset.mul_sum]
      _ ≤ 2 / Real.log x * ((2 * Real.log 4 + 16) * Real.sqrt x) := by
          have h2l : (0 : ℝ) ≤ 2 / Real.log x := by positivity
          exact mul_le_mul_of_nonneg_left (le_trans hsub hS) h2l
  -- assemble: multiply through by log x
  rw [le_div_iff₀ hlx]
  have e2 : 2 / Real.log x * ((2 * Real.log 4 + 16) * Real.sqrt x) * Real.log x
      = 2 * ((2 * Real.log 4 + 16) * Real.sqrt x) := by
    field_simp
  have hp1log : (∑ n ∈ Ioc 0 R, Λ n / (Real.sqrt n * Real.log n)) * Real.log x
      ≤ 8 * Real.sqrt x := by
    have step1 : (∑ n ∈ Ioc 0 R, Λ n / (Real.sqrt n * Real.log n)) * Real.log x
        ≤ (2 * Real.sqrt R) * Real.log x :=
      mul_le_mul_of_nonneg_right hpart1 hlx.le
    have step2 : (2 * Real.sqrt R) * Real.log x ≤ (2 * x ^ ((4 : ℝ)⁻¹)) * (4 * x ^ ((4 : ℝ)⁻¹)) := by
      have hsR0 : (0 : ℝ) ≤ Real.sqrt R := Real.sqrt_nonneg _
      nlinarith [hsqR, hlog, hlx, h14nn]
    have step3 : (2 * x ^ ((4 : ℝ)⁻¹)) * (4 * x ^ ((4 : ℝ)⁻¹)) = 8 * Real.sqrt x := by
      rw [← hq]; ring
    linarith
  have hp2log : (∑ n ∈ Ioc R ⌊x⌋₊, Λ n / (Real.sqrt n * Real.log n)) * Real.log x
      ≤ 2 * ((2 * Real.log 4 + 16) * Real.sqrt x) := by
    calc (∑ n ∈ Ioc R ⌊x⌋₊, Λ n / (Real.sqrt n * Real.log n)) * Real.log x
        ≤ 2 / Real.log x * ((2 * Real.log 4 + 16) * Real.sqrt x) * Real.log x :=
          mul_le_mul_of_nonneg_right hpart2 hlx.le
      _ = 2 * ((2 * Real.log 4 + 16) * Real.sqrt x) := e2
  have hfin : (∑ n ∈ Ioc 0 R, Λ n / (Real.sqrt n * Real.log n)
      + ∑ n ∈ Ioc R ⌊x⌋₊, Λ n / (Real.sqrt n * Real.log n)) * Real.log x
      = (∑ n ∈ Ioc 0 R, Λ n / (Real.sqrt n * Real.log n)) * Real.log x
        + (∑ n ∈ Ioc R ⌊x⌋₊, Λ n / (Real.sqrt n * Real.log n)) * Real.log x := by ring
  rw [hfin]
  nlinarith [hp1log, hp2log]

/-! ## [eq:cheb1], fourth bound: Σ_{n≤x} Λ(n)² ≪ x log x -/

/-- [eq:cheb1].4: Σ_{n≤x} Λ(n)² ≤ (log 4 + 4)·x·log x, from Λ(n) ≤ log n ≤ log x. -/
theorem sum_vonMangoldt_sq_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ^ 2 ≤ (Real.log 4 + 4) * x * Real.log x := by
  have h0 : (0 : ℝ) ≤ x := zero_le_one.trans hx
  have key : ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ^ 2 ≤ (∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n) * Real.log x := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun n hn => ?_
    obtain ⟨hn0, hnN⟩ := Finset.mem_Ioc.mp hn
    have hnx : (n : ℝ) ≤ x := le_trans (Nat.cast_le.mpr hnN) (Nat.floor_le h0)
    have h1 : Λ n ≤ Real.log x :=
      le_trans vonMangoldt_le_log (Real.log_le_log (by exact_mod_cast hn0) hnx)
    calc Λ n ^ 2 = Λ n * Λ n := pow_two _
      _ ≤ Λ n * Real.log x := mul_le_mul_of_nonneg_left h1 vonMangoldt_nonneg
  refine key.trans ?_
  have h2 : ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ≤ (Real.log 4 + 4) * x :=
    Chebyshev.psi_le_const_mul_self h0
  have h3 : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
  have h4 : (0 : ℝ) ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n :=
    Finset.sum_nonneg fun n _ => vonMangoldt_nonneg
  calc (∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n) * Real.log x
      ≤ ((Real.log 4 + 4) * x) * Real.log x := mul_le_mul_of_nonneg_right h2 h3
    _ = (Real.log 4 + 4) * x * Real.log x := by ring


/-! ## [eq:cheb2]: the two Mertens-type asymptotics

Mertens' first theorem Σ_{n≤x} Λ(n)/n = log x + O(1) is supplied by
`Mertens.sum_mangoldt_div_eq_log` (see
Zeta23/FromPNTPlus/Mertens.lean), so both [eq:cheb2] bounds are unconditional. -/

section Cheb2

open MeasureTheory

/-- Mertens' first theorem (von Mangoldt form): |Σ_{n≤x} Λ(n)/n − log x| ≤ log 4 + 4
for x ≥ 1.  Paper [lem:cheb] cites it as "Mertens' formula"; classical [MV07 §2.2]. -/
theorem mertensFirst {x : ℝ} (hx : 1 ≤ x) :
    |(∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n) - Real.log x| ≤ Real.log 4 + 4 :=
  Mertens.sum_mangoldt_div_eq_log hx

/-- Partial sums of Λ(n)/n, in the Icc form produced by Abel summation. -/
private noncomputable def Msum (t : ℝ) : ℝ := ∑ k ∈ Icc 0 ⌊t⌋₊, Λ k / k

/-- Partial sums of Λ(n)²/n, in the Icc form produced by Abel summation. -/
private noncomputable def M2sum (t : ℝ) : ℝ := ∑ k ∈ Icc 0 ⌊t⌋₊, Λ k ^ 2 / k

private lemma Msum_eq_Ioc (t : ℝ) : Msum t = ∑ k ∈ Ioc 0 ⌊t⌋₊, Λ k / k :=
  sum_Icc_eq_sum_Ioc (by simp) ⌊t⌋₊

private lemma M2sum_eq_Ioc (t : ℝ) : M2sum t = ∑ k ∈ Ioc 0 ⌊t⌋₊, Λ k ^ 2 / k :=
  sum_Icc_eq_sum_Ioc (by simp) ⌊t⌋₊

private lemma Msum_mono : Monotone Msum := fun _ _ hab =>
  Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor hab))
    fun n _ _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg n)

private lemma M2sum_mono : Monotone M2sum := fun _ _ hab =>
  Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc le_rfl (Nat.floor_le_floor hab))
    fun n _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg n)

private lemma Msum_nonneg (t : ℝ) : 0 ≤ Msum t :=
  Finset.sum_nonneg fun n _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg n)

private lemma M2sum_nonneg (t : ℝ) : 0 ≤ M2sum t :=
  Finset.sum_nonneg fun n _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg n)

/-- Abel summation with f = log, c n = Λ n / n. -/
private lemma abel_log_Msum {x : ℝ} (_hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log n * (Λ n / n)
      = Real.log x * ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n
        - ∫ t in Set.Ioc 1 x, t⁻¹ * Msum t := by
  have hf_diff : ∀ t ∈ Set.Icc (1 : ℝ) x, DifferentiableAt ℝ Real.log t := fun t ht =>
    Real.differentiableAt_log (by nlinarith [ht.1])
  have hf_int : IntegrableOn (deriv Real.log) (Set.Icc 1 x) := by
    rw [Real.deriv_log']
    refine ContinuousOn.integrableOn_Icc ?_
    exact continuousOn_inv₀.mono fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      nlinarith [ht.1]
  have habel := sum_mul_eq_sub_integral_mul₀ (fun n => Λ n / n) (by simp) x hf_diff hf_int
  have hL : ∑ k ∈ Icc 0 ⌊x⌋₊, Real.log k * ((fun n : ℕ => Λ n / n) k)
      = ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log n * (Λ n / n) := by
    rw [sum_Icc_eq_sum_Ioc (by simp) ⌊x⌋₊]
  have hR : ∑ k ∈ Icc 0 ⌊x⌋₊, (fun n : ℕ => Λ n / n) k
      = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n := by
    rw [sum_Icc_eq_sum_Ioc (by simp) ⌊x⌋₊]
  rw [hL, hR] at habel
  rw [habel]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  rw [Real.deriv_log]
  rfl

/-- Abel summation with f = log, c n = Λ n ^ 2 / n. -/
private lemma abel_log_M2sum {x : ℝ} (_hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log n * (Λ n ^ 2 / n)
      = Real.log x * ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n
        - ∫ t in Set.Ioc 1 x, t⁻¹ * M2sum t := by
  have hf_diff : ∀ t ∈ Set.Icc (1 : ℝ) x, DifferentiableAt ℝ Real.log t := fun t ht =>
    Real.differentiableAt_log (by nlinarith [ht.1])
  have hf_int : IntegrableOn (deriv Real.log) (Set.Icc 1 x) := by
    rw [Real.deriv_log']
    refine ContinuousOn.integrableOn_Icc ?_
    exact continuousOn_inv₀.mono fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      nlinarith [ht.1]
  have habel := sum_mul_eq_sub_integral_mul₀ (fun n => Λ n ^ 2 / n) (by simp) x hf_diff hf_int
  have hL : ∑ k ∈ Icc 0 ⌊x⌋₊, Real.log k * ((fun n : ℕ => Λ n ^ 2 / n) k)
      = ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log n * (Λ n ^ 2 / n) := by
    rw [sum_Icc_eq_sum_Ioc (by simp) ⌊x⌋₊]
  have hR : ∑ k ∈ Icc 0 ⌊x⌋₊, (fun n : ℕ => Λ n ^ 2 / n) k
      = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n := by
    rw [sum_Icc_eq_sum_Ioc (by simp) ⌊x⌋₊]
  rw [hL, hR] at habel
  rw [habel]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  rw [Real.deriv_log]
  rfl

private lemma integral_inv_Ioc {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in Set.Ioc 1 x, t⁻¹ = Real.log x := by
  rw [← intervalIntegral.integral_of_le hx, integral_inv ?h]
  · rw [div_one]
  case h =>
    rw [Set.uIcc_of_le hx]
    intro h
    rw [Set.mem_Icc] at h
    linarith [h.1]

private lemma integral_inv_mul_log {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in Set.Ioc 1 x, t⁻¹ * Real.log t = Real.log x ^ 2 / 2 := by
  rw [← intervalIntegral.integral_of_le hx]
  have hftc : ∀ t ∈ Set.uIcc (1 : ℝ) x,
      HasDerivAt (fun t : ℝ => Real.log t ^ 2 / 2) (t⁻¹ * Real.log t) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by nlinarith [ht.1]
    have h := ((Real.hasDerivAt_log ht0).pow 2).div_const 2
    have heq : t⁻¹ * Real.log t = ((2 : ℕ) : ℝ) * Real.log t ^ (2 - 1) * t⁻¹ / 2 := by
      push_cast
      ring
    rw [heq]
    exact h
  have hint : IntervalIntegrable (fun t : ℝ => t⁻¹ * Real.log t) volume 1 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    refine ContinuousOn.mul ?_ ?_
    · exact continuousOn_inv₀.mono fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        nlinarith [ht.1]
    · exact fun t ht => (Real.continuousAt_log (by nlinarith [ht.1])).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hftc hint]
  simp [Real.log_one]

private lemma integral_inv_mul_log_sq {x : ℝ} (hx : 1 ≤ x) :
    ∫ t in Set.Ioc 1 x, t⁻¹ * Real.log t ^ 2 = Real.log x ^ 3 / 3 := by
  rw [← intervalIntegral.integral_of_le hx]
  have hlogcont : ContinuousOn Real.log (Set.Icc 1 x) := fun t ht =>
    (Real.continuousAt_log (by nlinarith [ht.1])).continuousWithinAt
  have hftc : ∀ t ∈ Set.uIcc (1 : ℝ) x,
      HasDerivAt (fun t : ℝ => Real.log t ^ 3 / 3) (t⁻¹ * Real.log t ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by nlinarith [ht.1]
    have h := ((Real.hasDerivAt_log ht0).pow 3).div_const 3
    have heq : t⁻¹ * Real.log t ^ 2 = ((3 : ℕ) : ℝ) * Real.log t ^ (3 - 1) * t⁻¹ / 3 := by
      push_cast
      ring
    rw [heq]
    exact h
  have hint : IntervalIntegrable (fun t : ℝ => t⁻¹ * Real.log t ^ 2) volume 1 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    refine ContinuousOn.mul ?_ (hlogcont.pow 2)
    exact continuousOn_inv₀.mono fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      nlinarith [ht.1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hftc hint]
  simp [Real.log_one]

/-- Integrability of t⁻¹·M on (1, x] for a monotone nonnegative M. -/
private lemma integrableOn_inv_mul_mono {M : ℝ → ℝ} (hmono : Monotone M)
    (hnn : ∀ t, 0 ≤ M t) {x : ℝ} (_hx : 1 ≤ x) :
    IntegrableOn (fun t : ℝ => t⁻¹ * M t) (Set.Ioc 1 x) := by
  refine Integrable.mono' (g := fun _ => M x)
    (integrableOn_const (by simp)) ?_ ?_
  · exact (measurable_inv.mul hmono.measurable).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht1 : (1 : ℝ) < t := ht.1
    have hti : t⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right; linarith
    have h0 : (0 : ℝ) ≤ t⁻¹ := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (hnn t))]
    calc t⁻¹ * M t ≤ 1 * M t := mul_le_mul_of_nonneg_right hti (hnn t)
      _ = M t := one_mul _
      _ ≤ M x := hmono ht.2

/-- Partial summation step: Σ_{n≤x} log n · Λ(n)/n = (log x)²/2 + O(log x). -/
private lemma sum_log_mul_vonMangoldt_div_bound {x : ℝ} (hx : 1 ≤ x) :
    |(∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log n * (Λ n / n)) - Real.log x ^ 2 / 2|
      ≤ 2 * (Real.log 4 + 4) * Real.log x := by
  set K : ℝ := Real.log 4 + 4 with hK
  have hKpos : (0 : ℝ) < K := by rw [hK]; positivity
  have hlx : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
  have hMert : ∀ t : ℝ, 1 ≤ t → |Msum t - Real.log t| ≤ K := fun t ht => by
    rw [Msum_eq_Ioc]
    exact mertensFirst ht
  have habel := abel_log_Msum hx
  have hint_log : IntegrableOn (fun t : ℝ => t⁻¹ * Real.log t) (Set.Ioc 1 x) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    refine ContinuousOn.mul ?_ ?_
    · exact continuousOn_inv₀.mono fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        nlinarith [ht.1]
    · exact fun t ht => (Real.continuousAt_log (by nlinarith [ht.1])).continuousWithinAt
  have hint_M : IntegrableOn (fun t : ℝ => t⁻¹ * Msum t) (Set.Ioc 1 x) :=
    integrableOn_inv_mul_mono Msum_mono Msum_nonneg hx
  have hint_inv : IntegrableOn (fun t : ℝ => t⁻¹) (Set.Ioc 1 x) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    exact continuousOn_inv₀.mono fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      nlinarith [ht.1]
  have hint_diff : IntegrableOn (fun t : ℝ => t⁻¹ * (Msum t - Real.log t)) (Set.Ioc 1 x) :=
    ((hint_M.sub hint_log).congr_fun
      (fun t _ => by simp only [Pi.sub_apply]; ring) measurableSet_Ioc)
  have hsplit : ∫ t in Set.Ioc 1 x, t⁻¹ * Msum t
      = (∫ t in Set.Ioc 1 x, t⁻¹ * Real.log t)
        + ∫ t in Set.Ioc 1 x, t⁻¹ * (Msum t - Real.log t) := by
    rw [← MeasureTheory.integral_add hint_log hint_diff]
    exact setIntegral_congr_fun measurableSet_Ioc fun t _ => by ring
  have hE : |∫ t in Set.Ioc 1 x, t⁻¹ * (Msum t - Real.log t)| ≤ K * Real.log x := by
    have hb : ∀ᵐ t ∂(volume.restrict (Set.Ioc 1 x)),
        ‖t⁻¹ * (Msum t - Real.log t)‖ ≤ K * t⁻¹ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht1 : (1 : ℝ) ≤ t := ht.1.le
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ t⁻¹),
        mul_comm K t⁻¹]
      exact mul_le_mul_of_nonneg_left (hMert t ht1) (by positivity)
    calc |∫ t in Set.Ioc 1 x, t⁻¹ * (Msum t - Real.log t)|
        ≤ ∫ t in Set.Ioc 1 x, K * t⁻¹ := by
          rw [← Real.norm_eq_abs]
          exact norm_integral_le_of_norm_le (hint_inv.const_mul K) hb
      _ = K * ∫ t in Set.Ioc 1 x, t⁻¹ := MeasureTheory.integral_const_mul K _
      _ = K * Real.log x := by rw [integral_inv_Ioc hx]
  have hMx : |(∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n) - Real.log x| ≤ K := mertensFirst hx
  rw [habel, hsplit, integral_inv_mul_log hx]
  have harr : Real.log x * (∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n)
        - (Real.log x ^ 2 / 2 + ∫ t in Set.Ioc 1 x, t⁻¹ * (Msum t - Real.log t))
        - Real.log x ^ 2 / 2
      = Real.log x * ((∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n) - Real.log x)
        - ∫ t in Set.Ioc 1 x, t⁻¹ * (Msum t - Real.log t) := by ring
  rw [harr]
  have h1 : |Real.log x * ((∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n) - Real.log x)| ≤ Real.log x * K := by
    rw [abs_mul, abs_of_nonneg hlx]
    exact mul_le_mul_of_nonneg_left hMx hlx
  calc |Real.log x * ((∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n) - Real.log x)
        - ∫ t in Set.Ioc 1 x, t⁻¹ * (Msum t - Real.log t)|
      ≤ |Real.log x * ((∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n) - Real.log x)|
        + |∫ t in Set.Ioc 1 x, t⁻¹ * (Msum t - Real.log t)| := abs_sub _ _
    _ ≤ Real.log x * K + K * Real.log x := add_le_add h1 hE
    _ = 2 * K * Real.log x := by ring

/-! ### The proper-prime-power defect

[lem:cheb] proof: "Σ_{n≤x} Λ(n)²/n = Σ_{n≤x} Λ(n) log n/n + O(1) (the two differ
only at proper prime powers)".  The defect Σ_{n≤x} Λ(n)(log n − Λ(n))/n is
supported on prime powers pᵏ with k ≥ 2, where its value is (k−1)log²p/pᵏ;
summing over all p, k bounds it by an absolute constant. -/

private lemma sum_k_mul_half_pow_aux (K : ℕ) :
    (∑ k ∈ Icc 1 K, (k : ℝ) * (2⁻¹) ^ k) + ((K : ℝ) + 2) * (2⁻¹) ^ K ≤ 2 := by
  induction K with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]
    have hp : ((2 : ℝ)⁻¹) ^ (m + 1) = ((2 : ℝ)⁻¹) ^ m * (2 : ℝ)⁻¹ := pow_succ _ _
    push_cast
    nlinarith [ih, hp, pow_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹) m]

private lemma sum_k_mul_half_pow_le (K : ℕ) :
    ∑ k ∈ Icc 1 K, (k : ℝ) * (2⁻¹) ^ k ≤ 2 := by
  have h := sum_k_mul_half_pow_aux K
  nlinarith [h, pow_nonneg (by norm_num : (0 : ℝ) ≤ 2⁻¹) K,
    (by positivity : (0 : ℝ) ≤ (K : ℝ) + 2)]

/-- log²m/m² ≤ 64·(m^{7/4})⁻¹ for m ≥ 2 (via log m ≤ 8·m^{1/8}). -/
private lemma log_sq_div_sq_le {m : ℕ} (hm : 2 ≤ m) :
    Real.log m ^ 2 / (m : ℝ) ^ 2 ≤ 64 * ((m : ℝ) ^ ((7 : ℝ) / 4))⁻¹ := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by omega : 1 ≤ m)
  have hlog : Real.log m ≤ 8 * (m : ℝ) ^ ((8 : ℝ)⁻¹) := by
    have h8 := Real.log_le_rpow_div hm0.le (by norm_num : (0 : ℝ) < 8⁻¹)
    rw [div_eq_mul_inv, inv_inv] at h8
    linarith
  have h18nn : (0 : ℝ) ≤ (m : ℝ) ^ ((8 : ℝ)⁻¹) := Real.rpow_nonneg hm0.le _
  have hq8 : (m : ℝ) ^ ((8 : ℝ)⁻¹) * (m : ℝ) ^ ((8 : ℝ)⁻¹) = (m : ℝ) ^ ((4 : ℝ)⁻¹) := by
    rw [← Real.rpow_add hm0]; norm_num
  have hsq : Real.log m ^ 2 ≤ 64 * (m : ℝ) ^ ((4 : ℝ)⁻¹) := by
    nlinarith [hlog, Real.log_nonneg hm1, hq8, h18nn]
  have e : (m : ℝ) ^ ((4 : ℝ)⁻¹) / (m : ℝ) ^ 2 = ((m : ℝ) ^ ((7 : ℝ) / 4))⁻¹ := by
    rw [← Real.rpow_natCast (m : ℝ) 2, ← Real.rpow_sub hm0, ← Real.rpow_neg hm0.le]
    norm_num
  calc Real.log m ^ 2 / (m : ℝ) ^ 2
      ≤ 64 * (m : ℝ) ^ ((4 : ℝ)⁻¹) / (m : ℝ) ^ 2 := by gcongr
    _ = 64 * ((m : ℝ) ^ ((4 : ℝ)⁻¹) / (m : ℝ) ^ 2) := by ring
    _ = 64 * ((m : ℝ) ^ ((7 : ℝ) / 4))⁻¹ := by rw [e]

/-- Per-term bound for the defect: (k−1)·log²p/pᵏ ≤ 256·k·2⁻ᵏ·(p^{7/4})⁻¹. -/
private lemma defect_term_le {k p : ℕ} (hk : 1 ≤ k) (hp : p.Prime) :
    ((k : ℝ) - 1) * Real.log p ^ 2 / (p : ℝ) ^ k
      ≤ 256 * ((k : ℝ) * (2⁻¹) ^ k) * ((p : ℝ) ^ ((7 : ℝ) / 4))⁻¹ := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  rcases eq_or_lt_of_le hk with hk1 | hk2
  · rw [← hk1]
    norm_num
    positivity
  · have hk2' : 2 ≤ k := hk2
    have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hsplitpow : (p : ℝ) ^ k = (p : ℝ) ^ 2 * (p : ℝ) ^ (k - 2) := by
      rw [← pow_add]
      congr 1
      omega
    have hgepow : (2 : ℝ) ^ (k - 2) ≤ (p : ℝ) ^ (k - 2) :=
      pow_le_pow_left₀ (by norm_num) hp2 _
    have hden : (p : ℝ) ^ 2 * (2 : ℝ) ^ (k - 2) ≤ (p : ℝ) ^ k := by
      rw [hsplitpow]
      gcongr
    have hnum_nn : (0 : ℝ) ≤ ((k : ℝ) - 1) * Real.log p ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    have h1 : ((k : ℝ) - 1) * Real.log p ^ 2 / (p : ℝ) ^ k
        ≤ ((k : ℝ) - 1) * Real.log p ^ 2 / ((p : ℝ) ^ 2 * (2 : ℝ) ^ (k - 2)) := by
      gcongr
    have e1 : ((k : ℝ) - 1) * Real.log p ^ 2 / ((p : ℝ) ^ 2 * (2 : ℝ) ^ (k - 2))
        = (((k : ℝ) - 1) * ((2 : ℝ) ^ (k - 2))⁻¹) * (Real.log p ^ 2 / (p : ℝ) ^ 2) := by
      field_simp
    have e2 : ((2 : ℝ) ^ (k - 2))⁻¹ = 4 * ((2 : ℝ) ^ k)⁻¹ := by
      have h4 : (2 : ℝ) ^ (k - 2) * 4 = 2 ^ k := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_add]
        congr 1
        omega
      rw [← h4, mul_inv]
      field_simp
    have hfac_nn : (0 : ℝ) ≤ ((k : ℝ) - 1) * ((2 : ℝ) ^ (k - 2))⁻¹ :=
      mul_nonneg (by linarith) (by positivity)
    have hAP : (0 : ℝ) ≤ ((2 : ℝ) ^ k)⁻¹ * ((p : ℝ) ^ ((7 : ℝ) / 4))⁻¹ :=
      mul_nonneg (by positivity) (by positivity)
    calc ((k : ℝ) - 1) * Real.log p ^ 2 / (p : ℝ) ^ k
        ≤ ((k : ℝ) - 1) * Real.log p ^ 2 / ((p : ℝ) ^ 2 * (2 : ℝ) ^ (k - 2)) := h1
      _ = (((k : ℝ) - 1) * ((2 : ℝ) ^ (k - 2))⁻¹) * (Real.log p ^ 2 / (p : ℝ) ^ 2) := e1
      _ ≤ (((k : ℝ) - 1) * ((2 : ℝ) ^ (k - 2))⁻¹) * (64 * ((p : ℝ) ^ ((7 : ℝ) / 4))⁻¹) :=
          mul_le_mul_of_nonneg_left (log_sq_div_sq_le hp.two_le) hfac_nn
      _ = (((k : ℝ) - 1) * (4 * ((2 : ℝ) ^ k)⁻¹)) * (64 * ((p : ℝ) ^ ((7 : ℝ) / 4))⁻¹) := by
          rw [e2]
      _ ≤ 256 * ((k : ℝ) * (2⁻¹) ^ k) * ((p : ℝ) ^ ((7 : ℝ) / 4))⁻¹ := by
          rw [inv_pow]
          nlinarith [hAP]

/-- the telescoping step: for 2 ≤ m, (m^{7/4})⁻¹ ≤ 2(1/√(m−1) − 1/√m). -/
lemma rpow_inv_le_telescope {m : ℕ} (hm : 2 ≤ m) :
    ((m : ℝ) ^ ((7 : ℝ) / 4))⁻¹ ≤ 2 * (1 / Real.sqrt (m - 1) - 1 / Real.sqrt m) := by
  have hm1 : (1:ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.one_le_of_lt hm
  have hm0 : (0:ℝ) < m := by linarith
  have hm2 : (2:ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm10 : (0:ℝ) < (m : ℝ) - 1 := by linarith
  have hs : 0 < Real.sqrt ((m:ℝ) - 1) := Real.sqrt_pos.mpr hm10
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
  have hmono : Real.sqrt ((m:ℝ) - 1) ≤ Real.sqrt m := Real.sqrt_le_sqrt (by linarith)
  have h1 : Real.sqrt m * Real.sqrt m = (m:ℝ) := Real.mul_self_sqrt hm0.le
  have h2 : Real.sqrt ((m:ℝ) - 1) * Real.sqrt ((m:ℝ) - 1) = (m:ℝ) - 1 := Real.mul_self_sqrt hm10.le
  have hprod : (Real.sqrt m - Real.sqrt ((m:ℝ) - 1)) * (Real.sqrt m + Real.sqrt ((m:ℝ) - 1)) = 1 := by
    nlinarith [h1, h2]
  have hdiff : 1 / Real.sqrt ((m:ℝ) - 1) - 1 / Real.sqrt m
      = 1 / (Real.sqrt ((m:ℝ) - 1) * Real.sqrt m * (Real.sqrt m + Real.sqrt ((m:ℝ) - 1))) := by
    rw [div_sub_div _ _ hs.ne' hsm.ne', one_mul, mul_one]
    rw [show Real.sqrt m - Real.sqrt ((m:ℝ) - 1)
        = 1 / (Real.sqrt m + Real.sqrt ((m:ℝ) - 1)) from by
      rw [eq_div_iff (by positivity)]
      exact hprod]
    rw [div_div]
    ring_nf
  have hsq : Real.sqrt m = (m:ℝ) ^ ((1:ℝ)/2) := Real.sqrt_eq_rpow m
  have h32 : (m:ℝ) ^ ((3:ℝ)/2) = (m:ℝ) ^ ((1:ℝ)/2) * (m:ℝ) ^ ((1:ℝ)/2) * (m:ℝ) ^ ((1:ℝ)/2) := by
    rw [← Real.rpow_add hm0, ← Real.rpow_add hm0]
    norm_num
  have hden : Real.sqrt ((m:ℝ) - 1) * Real.sqrt m * (Real.sqrt m + Real.sqrt ((m:ℝ) - 1))
      ≤ 2 * (m:ℝ) ^ ((3:ℝ)/2) := by
    calc Real.sqrt ((m:ℝ) - 1) * Real.sqrt m * (Real.sqrt m + Real.sqrt ((m:ℝ) - 1))
        ≤ Real.sqrt m * Real.sqrt m * (2 * Real.sqrt m) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hmono hsm.le) (by linarith)
            (by positivity) (by positivity)
      _ = 2 * ((m:ℝ) ^ ((1:ℝ)/2) * (m:ℝ) ^ ((1:ℝ)/2) * (m:ℝ) ^ ((1:ℝ)/2)) := by
          rw [hsq]
          ring
      _ = 2 * (m:ℝ) ^ ((3:ℝ)/2) := by rw [h32]
  have h74 : (m:ℝ) ^ ((3:ℝ)/2) ≤ (m:ℝ) ^ ((7:ℝ)/4) :=
    Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num)
  rw [hdiff]
  calc ((m:ℝ) ^ ((7:ℝ)/4))⁻¹ = 1 / ((m:ℝ) ^ ((7:ℝ)/4)) := (one_div _).symm
    _ ≤ 1 / ((m:ℝ) ^ ((3:ℝ)/2)) := one_div_le_one_div_of_le (by positivity) h74
    _ = 2 * (1 / (2 * (m:ℝ) ^ ((3:ℝ)/2))) := by
        field_simp
    _ ≤ 2 * (1 / (Real.sqrt ((m:ℝ) - 1) * Real.sqrt m * (Real.sqrt m + Real.sqrt ((m:ℝ) - 1)))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact one_div_le_one_div_of_le (by positivity) hden

/-- partial sums with remainder: Σ_{m ≤ N} (m^{7/4})⁻¹ ≤ 3 − 2/√N for N ≥ 1. -/
lemma sum_range_rpow_inv_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ m ∈ Finset.range (N + 1), ((m : ℝ) ^ ((7 : ℝ) / 4))⁻¹ ≤ 3 - 2 / Real.sqrt N := by
  induction N with
  | zero => omega
  | succ n ih =>
      rcases Nat.eq_or_lt_of_le hN with h1 | h1
      · -- n + 1 = 1, i.e. n = 0: range 2 = {0, 1}
        have hn0 : n = 0 := by omega
        subst hn0
        norm_num [Finset.sum_range_succ, Real.sqrt_one]
      · -- n ≥ 1
        have hn1 : 1 ≤ n := by omega
        have htel := rpow_inv_le_telescope (m := n + 1) (by omega)
        have hcast : ((n + 1 : ℕ) : ℝ) - 1 = (n : ℝ) := by push_cast; ring
        rw [hcast] at htel
        rw [Finset.sum_range_succ]
        have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn1)
        have hs1 : 0 < Real.sqrt ((n:ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
        have hc2 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
        calc ∑ m ∈ Finset.range (n + 1), ((m : ℝ) ^ ((7 : ℝ) / 4))⁻¹
              + (((n + 1 : ℕ) : ℝ) ^ ((7 : ℝ) / 4))⁻¹
            ≤ (3 - 2 / Real.sqrt n) + 2 * (1 / Real.sqrt n - 1 / Real.sqrt ((n + 1 : ℕ) : ℝ)) := by
              exact add_le_add (ih hn1) htel
          _ = 3 - 2 / Real.sqrt ((n:ℝ) + 1) := by
              rw [hc2]
              field_simp
              ring
          _ = 3 - 2 / Real.sqrt ((n + 1 : ℕ) : ℝ) := by rw [hc2]

/-- Σ' m⁻⁷ᐟ⁴ ≤ 3. -/
lemma tsum_rpow_neg_seven_quarters_le :
    ∑' m : ℕ, ((m : ℝ) ^ ((7 : ℝ) / 4))⁻¹ ≤ 3 := by
  refine tsum_le_of_sum_range_le (fun n => by positivity) fun N => ?_
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0
    simp
  · obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    rcases Nat.eq_zero_or_pos M with h0 | hM
    · subst h0
      norm_num [Finset.sum_range_succ]
    · refine le_trans (sum_range_rpow_inv_le hM) ?_
      have : 0 < Real.sqrt M := Real.sqrt_pos.mpr (by exact_mod_cast hM)
      have h2 : 0 < 2 / Real.sqrt M := by positivity
      linarith

/-- The defect sum bounded by the explicit numeral 1537 = 512·3 + 1 (effective version;
uses the √-telescoping bound ζ-style Σ' m^{−7/4} ≤ 3 above). -/
lemma defect_bounded_explicit : ∀ x : ℝ,
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * (Real.log n - Λ n) / n ≤ 1537 := by
  intro x
  have hsum74 : Summable (fun m : ℕ => ((m : ℝ) ^ ((7 : ℝ) / 4))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (by norm_num)
  set B : ℝ := ∑' m : ℕ, ((m : ℝ) ^ ((7 : ℝ) / 4))⁻¹ with hB
  have hBnn : (0 : ℝ) ≤ B := tsum_nonneg fun m => by positivity
  have hB3 : B ≤ 3 := by
    rw [hB]
    exact tsum_rpow_neg_seven_quarters_le
  rcases lt_or_ge x 0 with hxneg | hx0
  · rw [Nat.floor_of_nonpos hxneg.le]
    simp only [Finset.Ioc_self, Finset.sum_empty]
    positivity
  have hvanish : ∀ n ∈ Ioc 0 ⌊x⌋₊, Λ n * (Real.log n - Λ n) / n ≠ 0 → IsPrimePow n := by
    intro n _ hne
    by_contra hnot
    rw [vonMangoldt_eq_zero_iff.mpr hnot] at hne
    simp at hne
  rw [← Finset.sum_filter_of_ne hvanish,
    Chebyshev.sum_PrimePow_eq_sum_sum (fun n => Λ n * (Real.log n - Λ n) / n) hx0]
  have hinner : ∀ k ∈ Icc 1 ⌊Real.log x / Real.log 2⌋₊,
      (∑ p ∈ Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ with p.Prime,
        Λ (p ^ k) * (Real.log ((p ^ k : ℕ) : ℝ) - Λ (p ^ k)) / ((p ^ k : ℕ) : ℝ))
        ≤ 256 * B * ((k : ℝ) * (2⁻¹) ^ k) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hk0 : k ≠ 0 := by omega
    have hstep : ∑ p ∈ Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ with p.Prime,
        Λ (p ^ k) * (Real.log ((p ^ k : ℕ) : ℝ) - Λ (p ^ k)) / ((p ^ k : ℕ) : ℝ)
        ≤ ∑ p ∈ Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ with p.Prime,
          256 * ((k : ℝ) * (2⁻¹) ^ k) * ((p : ℝ) ^ ((7 : ℝ) / 4))⁻¹ := by
      refine Finset.sum_le_sum fun p hp => ?_
      have hpp : p.Prime := (Finset.mem_filter.mp hp).2
      have hΛ : Λ (p ^ k) = Real.log p := by
        rw [vonMangoldt_apply_pow hk0, vonMangoldt_apply_prime hpp]
      have hlg : Real.log ((p ^ k : ℕ) : ℝ) = (k : ℝ) * Real.log p := by
        rw [Nat.cast_pow, Real.log_pow]
      have heq : Λ (p ^ k) * (Real.log ((p ^ k : ℕ) : ℝ) - Λ (p ^ k)) / ((p ^ k : ℕ) : ℝ)
          = ((k : ℝ) - 1) * Real.log p ^ 2 / (p : ℝ) ^ k := by
        rw [hΛ, hlg, Nat.cast_pow]
        ring
      rw [heq]
      exact defect_term_le hk1 hpp
    refine hstep.trans ?_
    rw [← Finset.mul_sum]
    have hs : (∑ p ∈ Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ with p.Prime,
        ((p : ℝ) ^ ((7 : ℝ) / 4))⁻¹) ≤ B :=
      hsum74.sum_le_tsum _ fun i _ => by positivity
    calc 256 * ((k : ℝ) * (2⁻¹) ^ k)
          * (∑ p ∈ Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ with p.Prime, ((p : ℝ) ^ ((7 : ℝ) / 4))⁻¹)
        ≤ 256 * ((k : ℝ) * (2⁻¹) ^ k) * B :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ = 256 * B * ((k : ℝ) * (2⁻¹) ^ k) := by ring
  refine le_trans (Finset.sum_le_sum hinner) ?_
  rw [← Finset.mul_sum]
  have h2 := sum_k_mul_half_pow_le ⌊Real.log x / Real.log 2⌋₊
  nlinarith [h2, hBnn, hB3]

/-- The defect sum is bounded by an absolute constant (from the explicit bound). -/
private lemma defect_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
      ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * (Real.log n - Λ n) / n ≤ C :=
  ⟨1537, by norm_num, defect_bounded_explicit⟩

/-- [eq:cheb2].1 with the constant explicit: C2a = 2(log 4 + 4) + 1537/log 2 (≤ 2230). -/
theorem sum_vonMangoldt_sq_div_eq_explicit : ∀ x : ℝ, 2 ≤ x →
    |(∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n) - Real.log x ^ 2 / 2|
      ≤ (2 * (Real.log 4 + 4) + 1537 / Real.log 2) * Real.log x := by
  set CD : ℝ := 1537 with hCDdef
  have hCD : ∀ y : ℝ, ∑ n ∈ Ioc 0 ⌊y⌋₊, Λ n * (Real.log n - Λ n) / n ≤ CD := by
    intro y
    rw [hCDdef]
    exact defect_bounded_explicit y
  have hCD0 : (0:ℝ) < CD := by rw [hCDdef]; norm_num
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  intro x hx
  show _ ≤ (2 * (Real.log 4 + 4) + CD / Real.log 2) * Real.log x
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have h1 := abs_le.mp (sum_log_mul_vonMangoldt_div_bound hx1)
  have hdiff : (∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log n * (Λ n / n))
        - ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n
      = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * (Real.log n - Λ n) / n := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hD0 : 0 ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n * (Real.log n - Λ n) / n :=
    Finset.sum_nonneg fun n _ =>
      div_nonneg (mul_nonneg vonMangoldt_nonneg (sub_nonneg.mpr vonMangoldt_le_log))
        (Nat.cast_nonneg n)
  have hDle := hCD x
  have hlog2 : Real.log 2 ≤ Real.log x := Real.log_le_log two_pos hx
  have hCDlog : CD ≤ CD / Real.log 2 * Real.log x := by
    have hkey : CD / Real.log 2 * Real.log 2 = CD := div_mul_cancel₀ CD hlog2pos.ne'
    calc CD = CD / Real.log 2 * Real.log 2 := hkey.symm
      _ ≤ CD / Real.log 2 * Real.log x :=
          mul_le_mul_of_nonneg_left hlog2 (by positivity)
  have hnn : (0 : ℝ) ≤ CD / Real.log 2 * Real.log x :=
    mul_nonneg (by positivity) (Real.log_nonneg hx1)
  rw [abs_le]
  constructor
  · nlinarith [h1.1, h1.2, hdiff, hD0, hDle, hCDlog, hnn]
  · nlinarith [h1.1, h1.2, hdiff, hD0, hDle, hCDlog, hnn]

/-- [eq:cheb2].1: Σ_{n≤x} Λ(n)²/n = (log x)²/2 + O(log x).
Paper [lem:cheb]: "Σ_{n≤x} Λ(n)²/n = Σ_{n≤x} Λ(n) log n/n + O(1) ..., and partial
summation from Mertens' formula gives Σ_{n≤x} Λ(n) log n/n = ½log²x + O(log x)."
(From the explicit-constant version.) -/
theorem sum_vonMangoldt_sq_div_eq :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |(∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n) - Real.log x ^ 2 / 2| ≤ C * Real.log x := by
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hlog4pos : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  exact ⟨_, by positivity, sum_vonMangoldt_sq_div_eq_explicit⟩

/-- [eq:cheb2].2 with the constant explicit: C2b = C2a/2 + 1/log 2. -/
theorem sum_vonMangoldt_sq_div_mul_log_sub_eq_explicit : ∀ x : ℝ, 2 ≤ x →
    |(∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n * (Real.log x - Real.log n)) -
        Real.log x ^ 3 / 6|
      ≤ ((2 * (Real.log 4 + 4) + 1537 / Real.log 2) / 2 + 1 / Real.log 2) * Real.log x ^ 2 := by
  set C2 : ℝ := 2 * (Real.log 4 + 4) + 1537 / Real.log 2 with hC2def
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hC2 : ∀ y : ℝ, 2 ≤ y → |(∑ n ∈ Ioc 0 ⌊y⌋₊, Λ n ^ 2 / n) - Real.log y ^ 2 / 2|
      ≤ C2 * Real.log y := by
    intro y hy
    rw [hC2def]
    exact sum_vonMangoldt_sq_div_eq_explicit y hy
  have hC20 : (0:ℝ) < C2 := by
    rw [hC2def]
    have h4 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  intro x hx
  show _ ≤ (C2 / 2 + 1 / Real.log 2) * Real.log x ^ 2
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hlx : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  -- the target sum equals ∫ t⁻¹ M2sum t
  have habel := abel_log_M2sum hx1
  have hident : ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n * (Real.log x - Real.log n)
      = ∫ t in Set.Ioc 1 x, t⁻¹ * M2sum t := by
    have e1 : ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n * (Real.log x - Real.log n)
        = Real.log x * (∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n)
          - ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log n * (Λ n ^ 2 / n) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [e1, habel]
    ring
  rw [hident]
  -- pointwise bound for the error density on (1, x]
  have hM2b : ∀ t ∈ Set.Ioc (1 : ℝ) x,
      |M2sum t - Real.log t ^ 2 / 2| ≤ C2 * Real.log t + 1 := by
    intro t ht
    have hlt0 : (0 : ℝ) ≤ Real.log t := Real.log_nonneg ht.1.le
    rcases le_or_gt 2 t with h2 | h2
    · have h := hC2 t h2
      rw [M2sum_eq_Ioc]
      have hC2log : (0 : ℝ) ≤ C2 * Real.log t := mul_nonneg hC20.le hlt0
      calc |(∑ n ∈ Ioc 0 ⌊t⌋₊, Λ n ^ 2 / n) - Real.log t ^ 2 / 2| ≤ C2 * Real.log t := h
        _ ≤ C2 * Real.log t + 1 := by linarith
    · have ht1 : (1 : ℝ) < t := ht.1
      have hfl : ⌊t⌋₊ = 1 := by
        rw [Nat.floor_eq_iff (by linarith : (0 : ℝ) ≤ t)]
        constructor
        · exact_mod_cast ht1.le
        · exact_mod_cast (by linarith : t < 1 + 1)
      have hM20 : M2sum t = 0 := by
        rw [M2sum_eq_Ioc, hfl]
        rw [show Finset.Ioc 0 1 = {1} from rfl]
        simp [vonMangoldt_apply_one]
      rw [hM20, zero_sub, abs_neg, abs_of_nonneg (by positivity)]
      have hlt2 : Real.log t ≤ Real.log 2 := Real.log_le_log (by linarith) h2.le
      have hl21 : Real.log 2 < 1 := by nlinarith [Real.log_two_lt_d9]
      nlinarith [mul_nonneg hC20.le hlt0]
  -- integrabilities
  have hcont_logsq : IntegrableOn (fun t : ℝ => t⁻¹ * (Real.log t ^ 2 / 2)) (Set.Ioc 1 x) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    have hlogcont : ContinuousOn Real.log (Set.Icc 1 x) := fun t ht =>
      (Real.continuousAt_log (by nlinarith [ht.1])).continuousWithinAt
    refine ContinuousOn.mul ?_ ((hlogcont.pow 2).div_const 2)
    exact continuousOn_inv₀.mono fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      nlinarith [ht.1]
  have hint_M2 : IntegrableOn (fun t : ℝ => t⁻¹ * M2sum t) (Set.Ioc 1 x) :=
    integrableOn_inv_mul_mono M2sum_mono M2sum_nonneg hx1
  have hint_diff : IntegrableOn
      (fun t : ℝ => t⁻¹ * (M2sum t - Real.log t ^ 2 / 2)) (Set.Ioc 1 x) :=
    ((hint_M2.sub hcont_logsq).congr_fun
      (fun t _ => by simp only [Pi.sub_apply]; ring) measurableSet_Ioc)
  have hsplit : ∫ t in Set.Ioc 1 x, t⁻¹ * M2sum t
      = (∫ t in Set.Ioc 1 x, t⁻¹ * (Real.log t ^ 2 / 2))
        + ∫ t in Set.Ioc 1 x, t⁻¹ * (M2sum t - Real.log t ^ 2 / 2) := by
    rw [← MeasureTheory.integral_add hcont_logsq hint_diff]
    exact setIntegral_congr_fun measurableSet_Ioc fun t _ => by ring
  have hval : ∫ t in Set.Ioc 1 x, t⁻¹ * (Real.log t ^ 2 / 2) = Real.log x ^ 3 / 6 := by
    have e : ∫ t in Set.Ioc 1 x, t⁻¹ * (Real.log t ^ 2 / 2)
        = ∫ t in Set.Ioc 1 x, (t⁻¹ * Real.log t ^ 2) * (1 / 2) :=
      setIntegral_congr_fun measurableSet_Ioc fun t _ => by ring
    rw [e, MeasureTheory.integral_mul_const, integral_inv_mul_log_sq hx1]
    ring
  -- error bound
  have hint_invlog : IntegrableOn (fun t : ℝ => t⁻¹ * Real.log t) (Set.Ioc 1 x) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    refine ContinuousOn.mul ?_ ?_
    · exact continuousOn_inv₀.mono fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        nlinarith [ht.1]
    · exact fun t ht => (Real.continuousAt_log (by nlinarith [ht.1])).continuousWithinAt
  have hint_inv : IntegrableOn (fun t : ℝ => t⁻¹) (Set.Ioc 1 x) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    exact continuousOn_inv₀.mono fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      nlinarith [ht.1]
  have hE : |∫ t in Set.Ioc 1 x, t⁻¹ * (M2sum t - Real.log t ^ 2 / 2)|
      ≤ C2 * (Real.log x ^ 2 / 2) + Real.log x := by
    have hg_int : IntegrableOn (fun t : ℝ => C2 * (t⁻¹ * Real.log t) + t⁻¹) (Set.Ioc 1 x) :=
      (hint_invlog.const_mul C2).add hint_inv
    have hb : ∀ᵐ t ∂(volume.restrict (Set.Ioc 1 x)),
        ‖t⁻¹ * (M2sum t - Real.log t ^ 2 / 2)‖ ≤ C2 * (t⁻¹ * Real.log t) + t⁻¹ := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have ht1 : (1 : ℝ) ≤ t := ht.1.le
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht1
      have hti : (0 : ℝ) ≤ t⁻¹ := by positivity
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hti]
      calc t⁻¹ * |M2sum t - Real.log t ^ 2 / 2| ≤ t⁻¹ * (C2 * Real.log t + 1) :=
            mul_le_mul_of_nonneg_left (hM2b t ht) hti
        _ = C2 * (t⁻¹ * Real.log t) + t⁻¹ := by ring
    calc |∫ t in Set.Ioc 1 x, t⁻¹ * (M2sum t - Real.log t ^ 2 / 2)|
        ≤ ∫ t in Set.Ioc 1 x, (C2 * (t⁻¹ * Real.log t) + t⁻¹) := by
          rw [← Real.norm_eq_abs]
          exact norm_integral_le_of_norm_le hg_int hb
      _ = C2 * (∫ t in Set.Ioc 1 x, t⁻¹ * Real.log t) + ∫ t in Set.Ioc 1 x, t⁻¹ := by
          rw [MeasureTheory.integral_add (hint_invlog.const_mul C2) hint_inv,
            MeasureTheory.integral_const_mul]
      _ = C2 * (Real.log x ^ 2 / 2) + Real.log x := by
          rw [integral_inv_mul_log hx1, integral_inv_Ioc hx1]
  -- assemble
  rw [hsplit, hval]
  have harr : Real.log x ^ 3 / 6
        + (∫ t in Set.Ioc 1 x, t⁻¹ * (M2sum t - Real.log t ^ 2 / 2))
        - Real.log x ^ 3 / 6
      = ∫ t in Set.Ioc 1 x, t⁻¹ * (M2sum t - Real.log t ^ 2 / 2) := by ring
  rw [harr]
  have hlogx2 : Real.log x ≤ Real.log x ^ 2 / Real.log 2 := by
    rw [le_div_iff₀ hlog2pos]
    have : Real.log 2 ≤ Real.log x := Real.log_le_log two_pos hx
    nlinarith [hlx]
  calc |∫ t in Set.Ioc 1 x, t⁻¹ * (M2sum t - Real.log t ^ 2 / 2)|
      ≤ C2 * (Real.log x ^ 2 / 2) + Real.log x := hE
    _ ≤ C2 * (Real.log x ^ 2 / 2) + Real.log x ^ 2 / Real.log 2 := by linarith
    _ = (C2 / 2 + 1 / Real.log 2) * Real.log x ^ 2 := by
        field_simp

/-- [eq:cheb2].2: Σ_{n≤x} (Λ(n)²/n)(log x − log n) = (log x)³/6 + O((log x)²).
Paper [lem:cheb]: "The second formula is ∫₁ˣ (Σ_{n≤t} Λ(n)²/n) dt/t."  (From the explicit-constant version.) -/
theorem sum_vonMangoldt_sq_div_mul_log_sub_eq :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |(∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n * (Real.log x - Real.log n)) -
          Real.log x ^ 3 / 6| ≤ C * Real.log x ^ 2 := by
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hlog4pos : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  exact ⟨_, by positivity, sum_vonMangoldt_sq_div_mul_log_sub_eq_explicit⟩

/-- The full H-cheb package [lem:cheb], instantiating the
`Zeta23.ChebyshevMertens` hypothesis structure of Hypotheses.lean.  Everything is
unconditional: Mathlib's Chebyshev ψ-bound + Abel summation + the Mertens
theorem (Zeta23/FromPNTPlus/Mertens.lean). -/
theorem chebyshevMertens : ChebyshevMertens where
  cheb1a := ⟨Real.log 4 + 4, fun x hx => sum_vonMangoldt_le (by linarith)⟩
  cheb1b := sum_vonMangoldt_div_sqrt_le_three
  cheb1c := ⟨4 * Real.log 4 + 40, fun x hx => sum_vonMangoldt_div_sqrt_mul_log_le hx⟩
  cheb1d := ⟨Real.log 4 + 4, fun x hx => sum_vonMangoldt_sq_le (by linarith)⟩
  cheb2a := by
    obtain ⟨C, _, h⟩ := sum_vonMangoldt_sq_div_eq
    exact ⟨C, fun x hx => h x hx⟩
  cheb2b := by
    obtain ⟨C, _, h⟩ := sum_vonMangoldt_sq_div_mul_log_sub_eq
    exact ⟨C, fun x hx => h x hx⟩

end Cheb2

end Cheb
end Zeta23
