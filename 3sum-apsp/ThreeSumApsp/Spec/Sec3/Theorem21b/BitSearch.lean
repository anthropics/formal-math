/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Spec.Sec3.Problems
public import ThreeSumApsp.Util.Flag

/-!
# The entries of a (min,+)-product, found bit by bit

Theorem 21(b), after [VW18, Theorem 4.2]: the (min,+)-product is computed
by a binary search for all entries at once.  An entry `c` with `-2U ≤ c ≤ 2U` is approached from
below: `bitLo U t c` is `c` with the lowest `t` bits of `c + 2U` cleared.

* The search starts at `t = R`, where `4U < 2^R`, with `-2U` (`bitLo_top`), and it ends at `t = 0`
  with `c` (`bitLo_zero`).
* One round goes from `t + 1` to `t`: it asks whether `c < bitLo U (t + 1) c + 2^t` and adds `2^t`
  if not (`bitLo_step`).
* The question is whether the pair `(i, j)` has a witness: `c` is below a number exactly if one of
  the sums `A[i,k] + B[k,j]` is (`exists_sum_lt_iff`).  So one round for all entries is one call of
  a routine that finds all pairs with a witness.
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-- Some sum `A[i,k] + B[k,j]` is below `z` exactly if the entry `(i, j)` of the product is. -/
theorem exists_sum_lt_iff {n : ℕ} (hn : 1 ≤ n) (A B : List ℤ) (i j : ℕ) (z : ℤ) :
    (∃ k < n, entry n A i k + entry n B k j < z) ↔ minPlusEntry n A B i j < z := by
  constructor
  · rintro ⟨k, hk, h⟩
    exact (minPlusEntry_le n A B i j hk).trans_lt h
  · intro h
    obtain ⟨k, hk, he⟩ := exists_minPlusEntry_eq hn A B i j
    exact ⟨k, hk, he ▸ h⟩

/-- `c` with the lowest `t` bits of `c + 2U` cleared. -/
def bitLo (U : ℤ) (t : ℕ) (c : ℤ) : ℤ := -(2 * U) + (((c + 2 * U).toNat / 2 ^ t * 2 ^ t : ℕ) : ℤ)

/-- With no bit cleared the number is `c`: the end of the search. -/
theorem bitLo_zero {U c : ℤ} (h : -(2 * U) ≤ c) : bitLo U 0 c = c := by
  rw [bitLo, pow_zero, Nat.div_one, Nat.mul_one, Int.toNat_of_nonneg (by linarith)]
  ring

/-- With all bits cleared the number is `-2U`: the start of the search. -/
theorem bitLo_top {U c : ℤ} {R : ℕ} (h : c + 2 * U < 2 ^ R) : bitLo U R c = -(2 * U) := by
  have hlt : (c + 2 * U).toNat < 2 ^ R := by
    rw [Int.toNat_lt' (by positivity)]
    exact_mod_cast h
  simp [bitLo, Nat.div_eq_of_lt hlt]

/-- The search never goes below `-2U`. -/
theorem le_bitLo (U : ℤ) (t : ℕ) (c : ℤ) : -(2 * U) ≤ bitLo U t c :=
  le_add_of_nonneg_right (Int.natCast_nonneg _)

/-- The search never goes above `c`. -/
theorem bitLo_le {U c : ℤ} (h : -(2 * U) ≤ c) (t : ℕ) : bitLo U t c ≤ c := by
  have hle : (c + 2 * U).toNat / 2 ^ t * 2 ^ t ≤ (c + 2 * U).toNat := Nat.div_mul_le_self _ _
  have hcast : ((c + 2 * U).toNat : ℤ) = c + 2 * U := Int.toNat_of_nonneg (by linarith)
  rw [bitLo]
  linarith [Int.ofNat_le.2 hle]

/-- Clearing one bit less: the bit number `t` of `y` is 0 exactly if `y` is less than `2^t` above
`y` with its lowest `t + 1` bits cleared. -/
private theorem div_mul_pow_step (y t : ℕ) :
    y / 2 ^ t * 2 ^ t = y / 2 ^ (t + 1) * 2 ^ (t + 1) +
      if y < y / 2 ^ (t + 1) * 2 ^ (t + 1) + 2 ^ t then 0 else 2 ^ t := by
  have hp : 0 < 2 ^ t := by positivity
  rw [pow_succ, ← Nat.div_div_eq_div_mul]
  generalize 2 ^ t = p at hp
  have hlow : y / p * p ≤ y := Nat.div_mul_le_self y p
  have hhigh : y < y / p * p + p := Nat.lt_div_mul_add hp
  generalize y / p = q at hlow hhigh
  rcases Nat.even_or_odd' q with ⟨b, rfl | rfl⟩
  · rw [show 2 * b / 2 = b by omega, show b * (p * 2) = 2 * b * p by ring, if_pos hhigh,
      Nat.add_zero]
  · have hle : b * (p * 2) + p ≤ y := (show _ = (2 * b + 1) * p by ring).trans_le hlow
    rw [show (2 * b + 1) / 2 = b by omega, if_neg (not_lt.2 hle)]
    ring

/-- **One round of the search**: `bitLo U t c` is `bitLo U (t + 1) c`, plus `2^t` unless
`c < bitLo U (t + 1) c + 2^t`. -/
theorem bitLo_step {U c : ℤ} (h : -(2 * U) ≤ c) (t : ℕ) :
    bitLo U t c = bitLo U (t + 1) c + 2 ^ t * (1 - flag (c < bitLo U (t + 1) c + 2 ^ t)) := by
  have hy : ((c + 2 * U).toNat : ℤ) = c + 2 * U := Int.toNat_of_nonneg (by linarith)
  have hstep := div_mul_pow_step (c + 2 * U).toNat t
  have hpow : ((2 ^ t : ℕ) : ℤ) = 2 ^ t := by push_cast; rfl
  simp only [bitLo, hstep]
  generalize (c + 2 * U).toNat = y at hy
  generalize y / 2 ^ (t + 1) * 2 ^ (t + 1) = z
  rw [← hpow]
  generalize 2 ^ t = p
  -- With `y = c + 2U` the question is whether `y < z + 2^t`.
  split_ifs with hlt
  · rw [flag_of (by omega)]
    push_cast
    ring
  · rw [flag_of_not (by omega)]
    push_cast
    ring

end ThreeSumApsp.Spec
