/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec2.Lemma11
public import ThreeSumApsp.Sec2.Tiling
public import ThreeSumApsp.Util.Choose
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Section 2.4.4: the two consequences of `N ≥ D^18`

Here `L = 19m`, `D = 4^m`, `N₀ = 3^{18m}` and `K = binom(19m, m)`.

* First consequence: `K₀ N₀ ≤ K N₀ ≤ D^18 ≤ N` (`K_mul_N0_le`, `K0_mul_N0_le`), so the padding at
  most doubles `N` (`padN_le_two_mul_of_D_pow_le`).  It follows from `binom(L, m) ≤ (eL/m)^m`
  (`Nat.choose_le_exp_mul_div_pow`) and `19e · 3^18 < 4^18` (`nineteen_mul_exp_mul_three_pow_lt`).
* Second consequence, equation (6): `10^L ≤ 2^{-m/9} N N₀` (`eq_6`).  It follows from
  `10^19 · 2^{1/9} / 3^18 < 4^18` (`ten_pow_mul_two_rpow_div_three_pow_lt`), raised to the power `m`
  (`ten_pow_div_N0_le`).
-/

public section

open Finset

namespace ThreeSumApsp

/-- Section 2.4.4: "using the general bound binom(L, m) ≤ (eL/m)^m, we have
K = binom(19m, m) ≤ (19e)^m".  The general bound is `Nat.choose_le_exp_mul_div_pow`.

NOTE.  The printed bound divides by `m`.  In Lean a quotient by 0 is 0 and `0^0 = 1`, so for `m = 0`
both sides are 1 and no hypothesis `m ≥ 1` is needed. -/
theorem K_le_pow (m : ℕ) : (K (19 * m) m : ℝ) ≤ (19 * Real.exp 1) ^ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [K]
  · have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    have hbase : Real.exp 1 * ((19 * m : ℕ) : ℝ) / (m : ℝ) = 19 * Real.exp 1 := by
      push_cast
      field_simp
    exact hbase ▸ Nat.choose_le_exp_mul_div_pow (19 * m) m

/-- Section 2.4.4: "19e · 3^18 < 4^18". -/
theorem nineteen_mul_exp_mul_three_pow_lt : 19 * Real.exp 1 * (3 : ℝ) ^ 18 < (4 : ℝ) ^ 18 := by
  calc 19 * Real.exp 1 * (3 : ℝ) ^ 18 < 19 * 2.7182818286 * (3 : ℝ) ^ 18 := by
        gcongr
        exact Real.exp_one_lt_d9
    _ < (4 : ℝ) ^ 18 := by norm_num

/-- `4^{18m} = D^18`. -/
private theorem four_pow_eq (m : ℕ) : ((4 : ℝ) ^ 18) ^ m = (D m : ℝ) ^ 18 := by
  rw [D, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, ← pow_mul, mul_comm]

/-- Section 2.4.4: "so K N₀ ≤ (19e · 3^18)^m ≤ 4^{18m}", and `4^{18m} = D^18`. -/
theorem K_mul_N0_le_D_pow (m : ℕ) : K (19 * m) m * N0 (19 * m) m ≤ D m ^ 18 := by
  have hK := K_le_pow m
  have key : (K (19 * m) m : ℝ) * (N0 (19 * m) m : ℝ) ≤ (D m : ℝ) ^ 18 := by
    calc (K (19 * m) m : ℝ) * (N0 (19 * m) m : ℝ)
        ≤ (19 * Real.exp 1) ^ m * ((3 : ℝ) ^ 18) ^ m := by
          rw [N0_nineteen_mul m]
          push_cast
          rw [pow_mul]
          exact mul_le_mul_of_nonneg_right hK (by positivity)
      _ = (19 * Real.exp 1 * (3 : ℝ) ^ 18) ^ m := (mul_pow _ _ _).symm
      _ ≤ ((4 : ℝ) ^ 18) ^ m :=
          pow_le_pow_left₀ (by positivity) nineteen_mul_exp_mul_three_pow_lt.le m
      _ = (D m : ℝ) ^ 18 := four_pow_eq m
  exact_mod_cast key

/-- Section 2.4.4, the first consequence of `N ≥ D^18`: "K N₀ ≤ D^18 ≤ N." -/
theorem K_mul_N0_le (m N : ℕ) (hN : D m ^ 18 ≤ N) : K (19 * m) m * N0 (19 * m) m ≤ N :=
  (K_mul_N0_le_D_pow m).trans hN

/-- Section 2.4.4, the first consequence of `N ≥ D^18`: "and hence K₀ N₀ ≤ K N₀ ≤ D^18 ≤ N." -/
theorem K0_mul_N0_le (m N : ℕ) (hN : D m ^ 18 ≤ N) : K0 (19 * m) m * N0 (19 * m) m ≤ N :=
  (Nat.mul_le_mul_right _ (Nat.sqrt_le_self _)).trans (K_mul_N0_le m N hN)

/-- Section 2.4.4: "This means the padding at most doubles N". -/
theorem padN_le_two_mul_of_D_pow_le (m N : ℕ) (hN : D m ^ 18 ≤ N) : padN (19 * m) m N ≤ 2 * N :=
  padN_le_two_mul (19 * m) m N (K0_mul_N0_le m N hN)

/-- Section 2.4.4: "10^19 · 2^{1/9} / 3^18 < 4^18". -/
theorem ten_pow_mul_two_rpow_div_three_pow_lt :
    (10 : ℝ) ^ 19 * (2 : ℝ) ^ (1 / 9 : ℝ) / (3 : ℝ) ^ 18 < (4 : ℝ) ^ 18 := by
  have htwo : (2 : ℝ) ^ (1 / 9 : ℝ) ≤ 2 := by
    calc (2 : ℝ) ^ (1 / 9 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := Real.rpow_one 2
  rw [div_lt_iff₀ (by positivity)]
  calc (10 : ℝ) ^ 19 * (2 : ℝ) ^ (1 / 9 : ℝ) ≤ (10 : ℝ) ^ 19 * 2 :=
        mul_le_mul_of_nonneg_left htwo (by positivity)
    _ < (4 : ℝ) ^ 18 * (3 : ℝ) ^ 18 := by norm_num

/-- Section 2.4.4: "so 10^L · 2^{m/9} / N₀ ≤ D^18", for `L = 19m`. -/
theorem ten_pow_div_N0_le (m : ℕ) :
    (10 : ℝ) ^ (19 * m) * (2 : ℝ) ^ ((m : ℝ) / 9) / (N0 (19 * m) m : ℝ) ≤ (D m : ℝ) ^ 18 := by
  have hroot : (2 : ℝ) ^ ((m : ℝ) / 9) = ((2 : ℝ) ^ (1 / 9 : ℝ)) ^ m := by
    rw [← Real.rpow_natCast _ m, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  calc (10 : ℝ) ^ (19 * m) * (2 : ℝ) ^ ((m : ℝ) / 9) / (N0 (19 * m) m : ℝ)
      = ((10 : ℝ) ^ 19 * (2 : ℝ) ^ (1 / 9 : ℝ) / (3 : ℝ) ^ 18) ^ m := by
        rw [N0_nineteen_mul m, hroot]
        push_cast
        rw [pow_mul, pow_mul, div_pow, mul_pow]
    _ ≤ ((4 : ℝ) ^ 18) ^ m := pow_le_pow_left₀ (by positivity)
        ten_pow_mul_two_rpow_div_three_pow_lt.le m
    _ = (D m : ℝ) ^ 18 := four_pow_eq m

/-- **Equation (6)**, the second consequence of `N ≥ D^18`: "10^L ≤ 2^{-m/9} N N₀", for
`L = 19m`. -/
theorem eq_6 (m N : ℕ) (hN : D m ^ 18 ≤ N) :
    (10 : ℝ) ^ (19 * m) ≤ (2 : ℝ) ^ (-(m : ℝ) / 9) * (N : ℝ) * (N0 (19 * m) m : ℝ) := by
  have hN0 : (0 : ℝ) < (N0 (19 * m) m : ℝ) := by exact_mod_cast N0_pos _ _
  have hN' : (D m : ℝ) ^ 18 ≤ (N : ℝ) := by exact_mod_cast hN
  have h := (ten_pow_div_N0_le m).trans hN'
  rw [div_le_iff₀ hN0] at h
  calc (10 : ℝ) ^ (19 * m)
      = (10 : ℝ) ^ (19 * m) * (2 : ℝ) ^ ((m : ℝ) / 9) * saving m := by
        rw [mul_assoc, mul_comm _ (saving m), saving_mul_two_rpow, mul_one]
    _ ≤ (N : ℝ) * (N0 (19 * m) m : ℝ) * saving m :=
        mul_le_mul_of_nonneg_right h (saving_pos m).le
    _ = saving m * (N : ℝ) * (N0 (19 * m) m : ℝ) := by ring

end ThreeSumApsp
