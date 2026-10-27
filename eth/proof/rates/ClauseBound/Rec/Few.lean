/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Computability.TuringMachine.Computable
public import Mathlib.Data.Int.Star
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.Tactic

/-! # A partial sum of binomial coefficients

Two bounds on a partial sum of binomial coefficients. For 0 ≤ y ≤ 1 and n ≤ δ, y^n·Σ_{ν≤n} C(δ, ν) ≤
(1 + y)^δ (`pow_mul_sum_choose_le`); hence, for 1 ≤ n ≤ δ and y = n/δ,
Σ_{ν≤n} C(δ, ν) ≤ y^(−n)·(1 + y)^δ ≤ y^(−n)·exp(n) ≤ (3δ/n)^n (`sum_choose_le`). -/

public section

namespace ClauseBound.Rec

open Finset

/-- For 0 ≤ y ≤ 1: y^n·Σ_{ν≤n} C(δ, ν) ≤ (1 + y)^δ, provided n ≤ δ. -/
theorem pow_mul_sum_choose_le {δ n : ℕ} (h2 : n ≤ δ) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    y ^ n * ∑ ν ∈ range (n + 1), (δ.choose ν : ℝ) ≤ (y + 1) ^ δ := by
  rw [add_pow, mul_sum]
  calc ∑ ν ∈ range (n + 1), y ^ n * (δ.choose ν : ℝ) ≤ ∑ ν ∈ range (n + 1), y ^ ν * 1 ^ (δ - ν) * (δ.choose ν : ℝ) := by
        refine sum_le_sum fun ν hν => ?_
        rw [one_pow, mul_one]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hy0 hy1 (by simpa [Nat.lt_succ_iff] using hν)) (by positivity)
    _ ≤ ∑ ν ∈ range (δ + 1), y ^ ν * 1 ^ (δ - ν) * (δ.choose ν : ℝ) :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega)) fun ν _ _ => by positivity

/-- For 1 ≤ n ≤ δ: Σ_{ν≤n} C(δ, ν) ≤ (3δ/n)^n. -/
theorem sum_choose_le {δ n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ δ) :
    (∑ ν ∈ range (n + 1), (δ.choose ν : ℝ)) ≤ (3 * δ / n) ^ n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast h1
  have hδ : (0 : ℝ) < δ := by exact_mod_cast (by omega : 0 < δ)
  have hy0 : (0 : ℝ) < n / δ := by positivity
  have hy1 : (n : ℝ) / δ ≤ 1 := (div_le_one hδ).2 (by exact_mod_cast h2)
  have h3 : ((n : ℝ) / δ + 1) ^ δ ≤ 3 ^ n := by
    calc ((n : ℝ) / δ + 1) ^ δ ≤ Real.exp ((n : ℝ) / δ) ^ δ := pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp _) _
      _ = Real.exp 1 ^ n := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, mul_one, mul_div_cancel₀ _ hδ.ne']
      _ ≤ 3 ^ n := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le _
  have h4 := (pow_mul_sum_choose_le h2 hy0.le hy1).trans h3
  have h5 : (3 * (δ : ℝ) / n) ^ n = 3 ^ n / ((n : ℝ) / δ) ^ n := by
    rw [← div_pow]
    congr 1
    field_simp
  rw [h5, le_div_iff₀ (by positivity), mul_comm]
  exact h4

end ClauseBound.Rec
