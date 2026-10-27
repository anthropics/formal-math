/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! # Time plus a polynomial in the length of the formula: the arithmetic

The padding machine halts within q·(a + 2^E + 1)^q steps on an input of length a, where E is the
exponent computed for the renamed formula, whose code has length b. `steps_split` bounds this by
q·2^q·(a + 1)^q, a polynomial
in a, plus 2q·(b + 2^E + 1)^(2q). Natural numbers only. -/

public section

namespace VariableBound.Rename

/-- q·(a + 2^E + 1)^q ≤ q·2^q·(a + 1)^q + 2q·(b + 2^E + 1)^(2q), for all natural numbers. -/
theorem steps_split (q a b E : ℕ) : q * (a + 2 ^ E + 1) ^ q ≤ q * 2 ^ q * (a + 1) ^ q + 2 * q * (b + 2 ^ E + 1) ^ (2 * q) := by
  have h1 : (a + 2 ^ E + 1) ^ q ≤ 2 ^ q * (a + 1) ^ q + 2 ^ q * (2 ^ E) ^ q := by
    rcases le_total (a + 1) (2 ^ E) with h | h
    · calc (a + 2 ^ E + 1) ^ q ≤ (2 * 2 ^ E) ^ q := Nat.pow_le_pow_left (by omega) q
        _ = 2 ^ q * (2 ^ E) ^ q := mul_pow _ _ _
        _ ≤ _ := Nat.le_add_left _ _
    · calc (a + 2 ^ E + 1) ^ q ≤ (2 * (a + 1)) ^ q := Nat.pow_le_pow_left (by omega) q
        _ = 2 ^ q * (a + 1) ^ q := mul_pow _ _ _
        _ ≤ _ := Nat.le_add_right _ _
  have h2 : 2 ^ q * (2 ^ E) ^ q ≤ (b + 2 ^ E + 1) ^ (2 * q) := by
    rw [two_mul, pow_add]
    have hE : 1 ≤ 2 ^ E := Nat.one_le_two_pow
    exact Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) q) (Nat.pow_le_pow_left (by omega) q)
  calc q * (a + 2 ^ E + 1) ^ q ≤ q * (2 ^ q * (a + 1) ^ q + (b + 2 ^ E + 1) ^ (2 * q)) := Nat.mul_le_mul_left _ (h1.trans (Nat.add_le_add_left h2 _))
    _ = q * 2 ^ q * (a + 1) ^ q + q * (b + 2 ^ E + 1) ^ (2 * q) := by ring
    _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _

/-- C·a^C grows with C, for a ≥ 1. -/
theorem poly_mono {C C' a : ℕ} (h : C ≤ C') (ha : 1 ≤ a) : C * a ^ C ≤ C' * a ^ C' :=
  Nat.mul_le_mul h (Nat.pow_le_pow_right ha h)

/-- q·2^q·(a + 1)^q ≤ C·a^C for C = q·4^q and a ≥ 1. -/
theorem poly_le (q : ℕ) {a : ℕ} (ha : 1 ≤ a) : q * 2 ^ q * (a + 1) ^ q ≤ q * 4 ^ q * a ^ (q * 4 ^ q) := by
  have h1 : (a + 1) ^ q ≤ 2 ^ q * a ^ q := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left (by omega) q
  have h2 : a ^ q ≤ a ^ (q * 4 ^ q) := Nat.pow_le_pow_right ha (Nat.le_mul_of_pos_right _ (by positivity))
  calc q * 2 ^ q * (a + 1) ^ q ≤ q * 2 ^ q * (2 ^ q * a ^ (q * 4 ^ q)) := Nat.mul_le_mul_left _ (h1.trans (Nat.mul_le_mul_left _ h2))
    _ = q * (2 * 2) ^ q * a ^ (q * 4 ^ q) := by rw [mul_pow]; ring
    _ = _ := by norm_num

end VariableBound.Rename
