/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import NetworkStatements

/-! Arithmetic for one level of the recursion (Section 5), in a form with other names than the
paper's: here ρ is the constant with 4ρ = log₂ 12 = 2 + log₂ 3, not the ρ = 11/12 of Lemma 2.
A name is the bit string that labels the bond of a rectangle between two merged nodes; it is written
in n + size(3^c) bits.
The file bounds the number of bits of 3^c, shows that the two names of a term, one for merged rows
and one for merged columns, have at most 4ρλ + 2 bits together,
and bounds the number C(g,2)² of rectangles by g⁴/4. -/

@[expose] public section

namespace Groundwork.GridArith

/-- The number 3^c has at most c·log₂3 + 1 bits. -/
theorem size_three_pow_le (c : ℕ) : ((Nat.size (3 ^ c) : ℕ) : ℝ) ≤ c * Real.logb 2 3 + 1 := by
  have hpos : 0 < Nat.size (3 ^ c) := Nat.size_pos.2 (by positivity)
  obtain ⟨s, hs⟩ : ∃ s, Nat.size (3 ^ c) = s + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  have h : 2 ^ s ≤ 3 ^ c := Nat.lt_size.1 (by omega)
  have h' : (2 : ℝ) ^ s ≤ (3 : ℝ) ^ c := by exact_mod_cast h
  have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h'
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h2
  rw [hs]
  push_cast
  linarith

/-- 4ρ = log₂ 12 = 2 + log₂ 3. -/
theorem four_rho : 4 * ρ = 2 + Real.logb 2 3 := by
  unfold ρ
  rw [show (12 : ℝ) = 2 ^ 2 * 3 by norm_num, Real.logb_mul (by norm_num) (by norm_num), Real.logb_pow,
    Real.logb_self_eq_one (by norm_num)]
  push_cast
  ring

/-- The two names of a term, with n = λ and d = i: the name for rows has n + size(3^(n−d)) bits, the
name for columns n + size(3^d) bits; together they have at most 4ρλ + 2 bits. -/
theorem cap_pair_le {n d : ℕ} (h : d ≤ n) :
    ((n + Nat.size (3 ^ (n - d)) + (n + Nat.size (3 ^ d)) : ℕ) : ℝ) ≤ 4 * ρ * n + 2 := by
  have h1 := size_three_pow_le (n - d)
  have h2 := size_three_pow_le d
  rw [Nat.cast_sub h] at h1
  rw [four_rho]
  push_cast
  nlinarith

/-- 4·C(g,2)² ≤ g⁴. -/
theorem four_mul_choose_sq_le (g : ℕ) : 4 * g.choose 2 ^ 2 ≤ g ^ 4 := by
  have h : 2 * g.choose 2 ≤ g ^ 2 := by
    rw [Nat.choose_two_right]
    calc 2 * (g * (g - 1) / 2) ≤ g * (g - 1) := Nat.mul_div_le _ _
      _ ≤ g * g := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = g ^ 2 := (sq g).symm
  calc 4 * g.choose 2 ^ 2 = (2 * g.choose 2) ^ 2 := by ring
    _ ≤ (g ^ 2) ^ 2 := Nat.pow_le_pow_left h 2
    _ = g ^ 4 := by ring

end Groundwork.GridArith
