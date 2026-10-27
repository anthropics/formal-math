/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.Choice
public import Mathlib.Data.Nat.Size
public import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # From which n on the overhead is paid for, and the choice of s from n

The algorithm for precision s has overheads that depend on Y = (3·K_t⁸)² and only mildly on n. This
file proves that an overhead of at most
c·Y^a·(√n + 1) is at most ⌊n/2^s⌋ as soon as n ≥ Y^(2a+2), and that s = sOf n ≥ 1 makes n that
large. Besides Params.lean, Seq.lean and Choice.lean
it uses Mathlib only. -/

public section

namespace PaddedDescent

/-! ### The number of binary digits against the square root -/

/-- The number of binary digits of n is at most 2·⌊√n⌋ + 2. -/
theorem size_le_sqrt (n : ℕ) : Nat.size n ≤ 2 * Nat.sqrt n + 2 := by
  rcases Nat.eq_zero_or_pos (Nat.size n) with h | h
  · omega
  obtain ⟨m, hm⟩ : ∃ m, Nat.size n = m + 1 := ⟨Nat.size n - 1, by omega⟩
  have h1 : 2 ^ m ≤ n := Nat.lt_size.1 (by omega)
  have h2 : 2 ^ (m / 2) ≤ Nat.sqrt n := by
    rw [Nat.le_sqrt, ← pow_add]
    exact le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) h1
  have h3 : m / 2 < 2 ^ (m / 2) := Nat.lt_two_pow_self
  omega

/-! ### The threshold -/

/-- 52s + 694 < Y (far from sharp). -/
theorem lin_lt_Ytop (s : ℕ) : 52 * s + 694 < Ytop s :=
  lt_of_lt_of_le Nat.lt_two_pow_self (Ytop_lower s)

/-- If n ≥ Y^(2a+2) then an overhead W ≤ c·Y^a·(⌊√n⌋+1), with c ≤ 2^500, satisfies W·2^s ≤ n. -/
theorem overhead_mul_le {s n W a c : ℕ} (hc : c ≤ 2 ^ 500) (hn : Ytop s ^ (2 * a + 2) ≤ n)
    (hW : W ≤ c * Ytop s ^ a * (Nat.sqrt n + 1)) : W * 2 ^ s ≤ n := by
  have hY : 2 ^ (52 * s + 694) ≤ Ytop s := Ytop_lower s
  have hY1 : 0 < Ytop s := Ytop_pos s
  have hq : Ytop s ^ (a + 1) ≤ Nat.sqrt n := by
    rw [Nat.le_sqrt, ← pow_add]
    exact le_trans (le_of_eq (by congr 1; ring)) hn
  have hq1 : 1 ≤ Nat.sqrt n := le_trans (Nat.one_le_pow _ _ hY1) hq
  have hcs : 2 * c * 2 ^ s ≤ Ytop s := by
    calc 2 * c * 2 ^ s ≤ 2 * 2 ^ 500 * 2 ^ s := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hc)
      _ = 2 ^ (1 + 500 + s) := by rw [pow_add, pow_add, pow_one]
      _ ≤ 2 ^ (52 * s + 694) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ Ytop s := hY
  calc W * 2 ^ s ≤ c * Ytop s ^ a * (Nat.sqrt n + 1) * 2 ^ s := Nat.mul_le_mul_right _ hW
    _ ≤ c * Ytop s ^ a * (2 * Nat.sqrt n) * 2 ^ s :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
    _ = 2 * c * 2 ^ s * (Ytop s ^ a * Nat.sqrt n) := by ring
    _ ≤ Ytop s * (Ytop s ^ a * Nat.sqrt n) := Nat.mul_le_mul_right _ hcs
    _ = Ytop s ^ (a + 1) * Nat.sqrt n := by ring
    _ ≤ Nat.sqrt n * Nat.sqrt n := Nat.mul_le_mul_right _ hq
    _ ≤ n := Nat.sqrt_le n

/-- The same with the division: W ≤ ⌊n/2^s⌋. -/
theorem overhead_le_div {s n W a c : ℕ} (hc : c ≤ 2 ^ 500) (hn : Ytop s ^ (2 * a + 2) ≤ n)
    (hW : W ≤ c * Ytop s ^ a * (Nat.sqrt n + 1)) : W ≤ n / 2 ^ s :=
  (Nat.le_div_iff_mul_le (by positivity)).2 (overhead_mul_le hc hn hW)

/-- Y^p ≤ 2^(2^(t+211)), t = depthOf s, for every p ≤ 2^200. -/
theorem Ytop_pow_le {p : ℕ} (hp : p ≤ 2 ^ 200) (s : ℕ) : Ytop s ^ p ≤ 2 ^ 2 ^ (depthOf s + 211) := by
  have key : 2 ^ (depthOf s + 11) * p ≤ 2 ^ (depthOf s + 211) := by
    calc 2 ^ (depthOf s + 11) * p ≤ 2 ^ (depthOf s + 11) * 2 ^ 200 := Nat.mul_le_mul_left _ hp
      _ = 2 ^ (depthOf s + 211) := by rw [← pow_add]
  calc Ytop s ^ p ≤ (2 ^ 2 ^ (depthOf s + 11)) ^ p := Nat.pow_le_pow_left (Ytop_le s) p
    _ = 2 ^ (2 ^ (depthOf s + 11) * p) := by rw [← pow_mul]
    _ ≤ 2 ^ 2 ^ (depthOf s + 211) := Nat.pow_le_pow_right (by norm_num) key

/-! ### The choice of s from n -/

/-- 2^(2^⌊log₂⌊log₂ n⌋⌋) ≤ n as soon as n ≥ 2. -/
theorem two_pow_two_pow_log2_log2_le {n : ℕ} (h : Nat.log2 n ≠ 0) : 2 ^ 2 ^ Nat.log2 (Nat.log2 n) ≤ n := by
  have hn : n ≠ 0 := by rintro rfl; simp at h
  exact le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.log2_self_le h)) (Nat.log2_self_le hn)

/-- If sOf n ≥ 1 then depthOf (sOf n) + 211 ≤ ⌊log₂⌊log₂ n⌋⌋. -/
theorem sOf_mul_add_le {n : ℕ} (h : 1 ≤ sOf n) : depthOf (sOf n) + 211 ≤ Nat.log2 (Nat.log2 n) := by
  unfold depthOf sOf at *; omega

/-- If sOf n ≥ 1 then 2^(2^(depthOf (sOf n) + 211)) ≤ n. -/
theorem two_pow_two_pow_sOf_le {n : ℕ} (h : 1 ≤ sOf n) : 2 ^ 2 ^ (depthOf (sOf n) + 211) ≤ n := by
  have h1 := sOf_mul_add_le h
  have h0 : Nat.log2 n ≠ 0 := by
    intro h0; rw [h0] at h1; simp at h1
  exact le_trans (Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) h1))
    (two_pow_two_pow_log2_log2_le h0)

/-- If sOf n ≥ 1 then Y^p ≤ n for Y = Ytop (sOf n) and every p ≤ 2^200. -/
theorem Ytop_sOf_pow_le {n p : ℕ} (hp : p ≤ 2 ^ 200) (h : 1 ≤ sOf n) : Ytop (sOf n) ^ p ≤ n :=
  (Ytop_pow_le hp (sOf n)).trans (two_pow_two_pow_sOf_le h)

/-- The threshold and the choice of s together: if sOf n ≥ 1 then an overhead W ≤ c·Y^a·(⌊√n⌋+1),
with Y = Ytop (sOf n), c ≤ 2^500 and
2a + 2 ≤ 2^200, is at most ⌊n/2^(sOf n)⌋. -/
theorem overhead_sOf_le_div {n W a c : ℕ} (h : 1 ≤ sOf n) (ha : 2 * a + 2 ≤ 2 ^ 200) (hc : c ≤ 2 ^ 500)
    (hW : W ≤ c * Ytop (sOf n) ^ a * (Nat.sqrt n + 1)) : W ≤ n / 2 ^ sOf n :=
  overhead_le_div hc (Ytop_sOf_pow_le ha h) hW

end PaddedDescent
