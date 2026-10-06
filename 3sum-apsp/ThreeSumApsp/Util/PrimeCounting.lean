/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.NumberTheory.Chebyshev

/-!
# Counting the primes up to m, in natural numbers

Three elementary bounds on the number `π(m)` of primes up to `m`, the cardinality of
`Nat.primesLE m`.

* `π(m) ≤ m` (`Nat.card_primesLE_le`).
* `m ≤ (⌊log₂ m⌋ + 1)(π(m) + 1)` (`Nat.le_log_mul_card_primesLE`), from the bound
  `2^m ≤ (m + 1) lcm(1, …, m)` of Mathlib: each prime power in the least common multiple is at most
  `m`.
* So there are at least `w` primes up to `(w + 1)(2⌊log₂(w + 1)⌋ + 4)`
  (`Nat.le_card_primesLE_mul_log`).
-/

public section

namespace Nat

open Finset

/-- There are at most `m` primes up to `m`. -/
theorem card_primesLE_le (m : ℕ) : #(Nat.primesLE m) ≤ m := by
  rw [Nat.primesLE_eq_filter_Icc_one]
  exact (card_filter_le _ _).trans_eq (by simp)

/-- A lower bound of Chebyshev's type in natural numbers: `m ≤ (⌊log₂ m⌋ + 1)(π(m) + 1)`. -/
theorem le_log_mul_card_primesLE (m : ℕ) : m ≤ (Nat.log 2 m + 1) * (#(Nat.primesLE m) + 1) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  set l := Nat.log 2 m
  have hlt : m < 2 ^ (l + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  refine (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp ?_
  calc 2 ^ m ≤ (m + 1) * Nat.lcmUpto m := Chebyshev.two_pow_le_mul_lcmUpto m
    _ = (m + 1) * ∏ p ∈ Nat.primesLE m, p ^ p.log m := by rw [Nat.lcmUpto_eq_prod_pow_log]
    _ ≤ 2 ^ (l + 1) * (2 ^ (l + 1)) ^ #(Nat.primesLE m) := Nat.mul_le_mul hlt
        (prod_le_pow_card _ _ _ fun p _ => (Nat.pow_log_le_self p hm.ne').trans hlt.le)
    _ = 2 ^ ((l + 1) * (#(Nat.primesLE m) + 1)) := by rw [← pow_succ', ← pow_mul]

/-- There are at least `w` primes up to `(w + 1)(2⌊log₂(w + 1)⌋ + 4)`. -/
theorem le_card_primesLE_mul_log (w : ℕ) :
    w ≤ #(Nat.primesLE ((w + 1) * (2 * Nat.log 2 (w + 1) + 4))) := by
  set a := Nat.log 2 (w + 1)
  set m := (w + 1) * (2 * a + 4) with hm
  have hw : w + 1 < 2 ^ (a + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have ha : 2 * a + 4 ≤ 2 ^ (a + 2) := by
    have := Nat.lt_two_pow_self (n := a + 1)
    rw [pow_succ]
    omega
  have hlog : Nat.log 2 m < 2 * a + 3 := Nat.log_lt_of_lt_pow (by positivity) <|
    calc m < 2 ^ (a + 1) * 2 ^ (a + 2) := Nat.mul_lt_mul_of_lt_of_le hw ha (by positivity)
      _ = 2 ^ (2 * a + 3) := by rw [← pow_add]; congr 1; omega
  have hlt : (2 * a + 3) * (w + 1) < (2 * a + 3) * (#(Nat.primesLE m) + 1) :=
    calc (2 * a + 3) * (w + 1) < (2 * a + 4) * (w + 1) :=
          Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
      _ = m := mul_comm _ _
      _ ≤ (Nat.log 2 m + 1) * (#(Nat.primesLE m) + 1) := le_log_mul_card_primesLE m
      _ ≤ (2 * a + 3) * (#(Nat.primesLE m) + 1) := Nat.mul_le_mul_right _ hlog
  have := Nat.lt_of_mul_lt_mul_left hlt
  omega

end Nat
