/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Binomial coefficients

Upper bounds. A single summand of the binomial expansion of `(a + b) ^ n` is at most the whole sum
(`Nat.choose_mul_pow_mul_pow_le`); with `a = 1` this is `binom(n, k) * b ^ (n - k) ≤ (b + 1) ^ n`
(`Nat.choose_mul_pow_le`), which the paper uses with `b = 9`. And `binom(n, k) ≤ (e n / k) ^ k`
(`Nat.choose_le_exp_mul_div_pow`).

A lower bound. For `k ≤ n`, the largest of the `n + 1` terms `binom(n, j) k^j (n-k)^{n-j}` of the
expansion of `n^n = (k + (n-k))^n` is the one with `j = k`: the terms increase up to `j = k` and
decrease from there on. This gives the standard lower bound on a binomial coefficient
(`Nat.pow_self_le_mul_choose_mul_pow_mul_pow`), which Section 4.4 uses in the proof of Corollary 26
and, written with the entropy function as `e^{n H(k/n)}/(n+1) ≤ binom(n, k)`, in the proof of
Corollary 31.
-/

public section

namespace Nat

/-! ## Upper bounds -/

/-- One summand of the binomial expansion of `(a + b) ^ n` is at most `(a + b) ^ n`. -/
theorem choose_mul_pow_mul_pow_le (a b n k : ℕ) :
    n.choose k * a ^ k * b ^ (n - k) ≤ (a + b) ^ n := by
  obtain hk | hk := le_or_gt k n
  · rw [add_pow]
    calc n.choose k * a ^ k * b ^ (n - k) = a ^ k * b ^ (n - k) * n.choose k := by ring
      _ ≤ _ := Finset.single_le_sum (f := fun k => a ^ k * b ^ (n - k) * n.choose k)
          (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
  · rw [Nat.choose_eq_zero_of_lt hk, zero_mul, zero_mul]
    exact Nat.zero_le _

/-- `binom(n, k) * b ^ (n - k) ≤ (b + 1) ^ n`. -/
theorem choose_mul_pow_le (b n k : ℕ) : n.choose k * b ^ (n - k) ≤ (b + 1) ^ n := by
  simpa only [one_pow, mul_one, add_comm] using choose_mul_pow_mul_pow_le 1 b n k

/-- `binom(n, k) ≤ (e n / k) ^ k`: indeed `binom(n, k) ≤ n ^ k / k!`, and
`k ^ k / k! ≤ e ^ k` is one term of the exponential series. For `k = 0` both sides are `1`. -/
theorem choose_le_exp_mul_div_pow (n k : ℕ) :
    (n.choose k : ℝ) ≤ (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k := by
  obtain rfl | hk := k.eq_zero_or_pos
  · rw [choose_zero_right, pow_zero, cast_one]
  have hk' : (0 : ℝ) < k := cast_pos.2 hk
  have hfact : (0 : ℝ) < k.factorial := cast_pos.2 k.factorial_pos
  have hexp : (k : ℝ) ^ k ≤ Real.exp k * k.factorial :=
    (div_le_iff₀ hfact).1 (Real.pow_div_factorial_le_exp _ hk'.le k)
  rw [div_pow, mul_pow, ← Real.exp_nat_mul, mul_one]
  refine (choose_le_pow_div k n).trans ?_
  rw [div_le_div_iff₀ hfact (pow_pos hk' k)]
  calc (n : ℝ) ^ k * (k : ℝ) ^ k ≤ (n : ℝ) ^ k * (Real.exp k * k.factorial) :=
        mul_le_mul_of_nonneg_left hexp (pow_nonneg n.cast_nonneg k)
    _ = Real.exp k * (n : ℝ) ^ k * k.factorial := by ring

/-! ## The largest term of a binomial expansion -/

/-- The term number `j` of the expansion of `n^n = (k + (n-k))^n`. -/
private def modeTerm (n k j : ℕ) : ℕ := n.choose j * k ^ j * (n - k) ^ (n - j)

/-- The quotient of two consecutive terms is `(n - j) k / ((n - k) (j + 1))`. -/
private theorem modeTerm_succ_mul {n j : ℕ} (k : ℕ) (hj : j < n) :
    modeTerm n k (j + 1) * ((n - k) * (j + 1)) = modeTerm n k j * ((n - j) * k) := by
  have he : n - j = n - (j + 1) + 1 := by omega
  calc modeTerm n k (j + 1) * ((n - k) * (j + 1))
      = n.choose (j + 1) * (j + 1) * k ^ (j + 1) * (n - k) ^ (n - (j + 1) + 1) := by
        rw [modeTerm]; ring
    _ = n.choose j * (n - j) * k ^ (j + 1) * (n - k) ^ (n - j) := by
        rw [Nat.choose_succ_right_eq, ← he]
    _ = modeTerm n k j * ((n - j) * k) := by rw [modeTerm]; ring

/-- The terms increase up to `j = k`. -/
private theorem modeTerm_le_succ {n k j : ℕ} (hjk : j < k) (hkn : k ≤ n) :
    modeTerm n k j ≤ modeTerm n k (j + 1) := by
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.mul_pos (by omega : 0 < n - j) (by omega : 0 < k))
  rw [← modeTerm_succ_mul k (by omega)]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))

/-- The terms decrease from `j = k` on. -/
private theorem modeTerm_succ_le {n k j : ℕ} (hkj : k ≤ j) (hjn : j < n) :
    modeTerm n k (j + 1) ≤ modeTerm n k j := by
  refine Nat.le_of_mul_le_mul_right ?_ (Nat.mul_pos (by omega : 0 < n - k) j.succ_pos)
  rw [modeTerm_succ_mul k hjn]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (by omega) (by omega))

/-- Every term is at most the term with `j = k`. -/
private theorem modeTerm_le_mode {n k j : ℕ} (hkn : k ≤ n) (hjn : j ≤ n) :
    modeTerm n k j ≤ modeTerm n k k := by
  rcases le_total j k with hjk | hkj
  · induction hjk using Nat.decreasingInduction with
    | self => rfl
    | of_succ j hjk ih => exact (modeTerm_le_succ hjk hkn).trans (ih (by omega))
  · induction j, hkj using Nat.le_induction with
    | base => rfl
    | succ j hkj ih => exact (modeTerm_succ_le hkj hjn).trans (ih (by omega))

/-- Proof of Corollary 26: "the standard bound binom(n, k) ≥ 1/(n+1) · n^n/(k^k (n-k)^{n-k})",
without fractions.  Of the `n + 1` terms of the expansion of `n^n = (k + (n-k))^n`, the one with
`binom(n, k)` is the largest. -/
theorem pow_self_le_mul_choose_mul_pow_mul_pow {n k : ℕ} (hkn : k ≤ n) :
    n ^ n ≤ (n + 1) * (n.choose k * k ^ k * (n - k) ^ (n - k)) :=
  calc n ^ n = (k + (n - k)) ^ n := by rw [Nat.add_sub_cancel' hkn]
    _ = ∑ j ∈ Finset.range (n + 1), modeTerm n k j := by
        rw [add_pow]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [modeTerm, Nat.cast_id]
        ring
    _ ≤ ∑ _j ∈ Finset.range (n + 1), modeTerm n k k :=
        Finset.sum_le_sum fun _ hj => modeTerm_le_mode hkn (Finset.mem_range_succ_iff.1 hj)
    _ = (n + 1) * (n.choose k * k ^ k * (n - k) ^ (n - k)) := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul, modeTerm]

end Nat
