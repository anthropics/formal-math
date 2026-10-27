/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! # One constant for a polynomial bound

Definition 4 and Lemma 1 write their polynomial factors as C·(B + λ)^C and C₁·(P + B)^{C₁}, one
constant for factor and exponent. The theorems of this development give bounds of the form s +
a·y^a, where s and y are at most linear in x = B + λ. These lemmas put such a bound under Cc·x^Cc,
with a ≤ Cc, so that the bound on the time can be raised to the same constant. -/

public section

namespace Printed

/-- For all a and k there is Cc ≥ a with k·x + a·(k·x)^a ≤ Cc·x^Cc for all x ≥ 1. -/
theorem absorb (a k : ℕ) : ∃ Cc : ℕ, a ≤ Cc ∧ ∀ x : ℕ, 1 ≤ x → k * x + a * (k * x) ^ a ≤ Cc * x ^ Cc := by
  refine ⟨k + a * k ^ a + a + 1, by omega, fun x hx => ?_⟩
  have h1 : x ≤ x ^ (k + a * k ^ a + a + 1) := Nat.le_self_pow (by omega) x
  have h2 : x ^ a ≤ x ^ (k + a * k ^ a + a + 1) := Nat.pow_le_pow_right hx (by omega)
  calc k * x + a * (k * x) ^ a = k * x + a * k ^ a * x ^ a := by rw [mul_pow]; ring
    _ ≤ k * x ^ (k + a * k ^ a + a + 1) + a * k ^ a * x ^ (k + a * k ^ a + a + 1) := Nat.add_le_add (Nat.mul_le_mul_left _ h1) (Nat.mul_le_mul_left _ h2)
    _ = (k + a * k ^ a) * x ^ (k + a * k ^ a + a + 1) := by ring
    _ ≤ (k + a * k ^ a + a + 1) * x ^ (k + a * k ^ a + a + 1) := Nat.mul_le_mul_right _ (by omega)

/-- The same for any s and y that are at most k·x. -/
theorem absorb_le (a k : ℕ) : ∃ Cc : ℕ, a ≤ Cc ∧ ∀ x s y : ℕ, 1 ≤ x → s ≤ k * x → y ≤ k * x → s + a * y ^ a ≤ Cc * x ^ Cc := by
  obtain ⟨Cc, h1, h2⟩ := absorb a k
  exact ⟨Cc, h1, fun x s y hx hs hy => (Nat.add_le_add hs (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hy _))).trans (h2 x hx)⟩

/-- A bound a·p·x^a on the time may be raised to Cc·p·x^Cc, for a ≤ Cc and x ≥ 1. -/
theorem absorb_time {a Cc : ℕ} (h : a ≤ Cc) {p x : ℝ} (hp : 0 ≤ p) (hx : 1 ≤ x) : (a : ℝ) * p * x ^ a ≤ Cc * p * x ^ Cc := by
  have h1 : (a : ℝ) ≤ Cc := by exact_mod_cast h
  have h2 : x ^ a ≤ x ^ Cc := pow_le_pow_right₀ hx h
  have hx0 : 0 ≤ x := by linarith
  exact mul_le_mul (mul_le_mul_of_nonneg_right h1 hp) h2 (pow_nonneg hx0 a) (mul_nonneg (Nat.cast_nonneg _) hp)

end Printed
