/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.ParityChecks.ProgDefs
public import ClauseBound.ParityChecks.Params

/-! # Bit lengths for Δ = 2^β

Facts on ⌈log₂⌉ and on the bit length, and bounds on the block length `blkOL (2 ^ β)` and on the bit
length of `blkOL (2 ^ β) * (7 * n + 1)`, for Δ = 2^β. -/

public section

namespace ClauseBound.ParityChecks

/-- ⌈log₂(2·2^β)⌉ = β + 1. -/
theorem LD_two_pow (β : ℕ) : LD (2 ^ β) = β + 1 := by
  rw [LD, ← pow_succ', Nat.clog_pow 2 _ (by norm_num)]

/-- The bit length of 2^β·n. -/
theorem size_mul_le (β n : ℕ) : Nat.size (2 ^ β * n) ≤ β + Nat.size n := by
  rw [Nat.size_le, pow_add]
  exact Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self n) (by positivity)

/-- ⌈log₂ n⌉ is at most the bit length of n. -/
theorem clog_le_size (n : ℕ) : Nat.clog 2 n ≤ Nat.size n :=
  Nat.clog_le_of_le_pow (Nat.lt_size_self n).le

/-- The length of a block for Δ = 2^β is at most 2^{2β+5}. -/
theorem blkOL_two_pow_le (β : ℕ) : blkOL (2 ^ β) ≤ 2 ^ (2 * β + 5) := by
  rw [blkOL, LD_two_pow]
  have h1 : β + 1 ≤ 2 ^ β := Nat.lt_two_pow_self
  have h2 : 1 ≤ 2 ^ β := Nat.one_le_two_pow
  have e : 2 ^ (2 * β + 5) = 32 * (2 ^ β * 2 ^ β) := by
    rw [show 2 * β + 5 = β + β + 5 by ring, pow_add, pow_add]; ring
  rw [e]
  generalize 2 ^ β = E at *
  have h3 : 16 * E * (β + 1) ≤ 16 * E * E := Nat.mul_le_mul_left _ h1
  have h4 : E ≤ E * E := Nat.le_mul_of_pos_left _ h2
  nlinarith

/-- The bit length of the number of clauses of the three layers, for Δ = 2^β. -/
theorem size_blk_le (β n : ℕ) : Nat.size (blkOL (2 ^ β) * (7 * n + 1)) ≤ 2 * β + Nat.size n + 10 := by
  rw [Nat.size_le]
  have h1 := blkOL_two_pow_le β
  have h2 : 7 * n + 1 ≤ 2 ^ (Nat.size n + 3) := by
    have := Nat.lt_size_self n
    rw [pow_add]
    omega
  calc blkOL (2 ^ β) * (7 * n + 1) ≤ 2 ^ (2 * β + 5) * 2 ^ (Nat.size n + 3) := Nat.mul_le_mul h1 h2
    _ = 2 ^ (2 * β + Nat.size n + 8) := by rw [← pow_add]; congr 1; ring
    _ < 2 ^ (2 * β + Nat.size n + 10) := Nat.pow_lt_pow_right (by norm_num) (by omega)

end ClauseBound.ParityChecks
