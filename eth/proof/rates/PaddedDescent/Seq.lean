/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.Params
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! # The sequence K_j

K_j = 2^(k_j) with k_j = 104·2^j − 2j − 96 in closed form; K_{j+1} = g_j²; K_j lies between 256·4^j
and 2^(104·2^j); small facts about K_j, g_j and
the numbers K_t, Y of the top level. Besides Params.lean it uses Mathlib only. -/

public section

namespace PaddedDescent

/-! ### The exponents k_j -/

/-- The closed form: k_j + 2j + 96 = 104·2^j. -/
theorem kseq_closed (j : ℕ) : kseq j + 2 * j + 96 = 104 * 2 ^ j := by
  induction j with
  | zero => rw [kseq_zero]; norm_num
  | succ j ih => rw [kseq_succ, pow_succ]; omega

/-- 94j + 8 ≤ k_j. -/
theorem kseq_ge (j : ℕ) : 94 * j + 8 ≤ kseq j := by
  have h1 := kseq_closed j
  have h2 : j < 2 ^ j := Nat.lt_two_pow_self
  omega

/-- k_j ≤ 104·2^j. -/
theorem kseq_le (j : ℕ) : kseq j ≤ 104 * 2 ^ j := by
  have h1 := kseq_closed j
  omega

/-- k_j grows strictly with j. -/
theorem kseq_strictMono : StrictMono kseq :=
  strictMono_nat_of_lt_succ fun j => by rw [kseq_succ]; omega

/-! ### K_j and g_j -/

/-- K₀ = 256. -/
theorem Kseq_zero : Kseq 0 = 256 := by rw [Kseq, kseq_zero]; norm_num

/-- g_j = 2^(k_j + 47 + j). -/
theorem gseq_eq (j : ℕ) : gseq j = 2 ^ (kseq j + 47 + j) := by
  rw [gseq, Kseq, Lseq, ← pow_add, add_assoc]

/-- K_{j+1} = g_j·g_j. -/
theorem Kseq_succ_eq_mul (j : ℕ) : Kseq (j + 1) = gseq j * gseq j := by
  rw [gseq_eq, ← pow_add, Kseq, kseq_succ, two_mul]

/-- K_{j+1} = g_j². -/
theorem Kseq_succ_eq_sq (j : ℕ) : Kseq (j + 1) = gseq j ^ 2 := by
  rw [Kseq_succ_eq_mul, sq]

/-- Lower bound: 256·4^j ≤ K_j. -/
theorem Kseq_lower (j : ℕ) : 256 * 4 ^ j ≤ Kseq j := by
  have h := kseq_ge j
  calc 256 * 4 ^ j = 2 ^ (8 + 2 * j) := by rw [pow_add, pow_mul]; norm_num
    _ ≤ 2 ^ kseq j := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- 256 ≤ K_j. -/
theorem Kseq_ge (j : ℕ) : 256 ≤ Kseq j :=
  le_trans (Nat.le_mul_of_pos_right _ (by positivity)) (Kseq_lower j)

/-- K_j is positive. -/
theorem Kseq_pos (j : ℕ) : 0 < Kseq j := lt_of_lt_of_le (by norm_num) (Kseq_ge j)

/-- Upper bound: K_j ≤ 2^(104·2^j). -/
theorem Kseq_upper (j : ℕ) : Kseq j ≤ 2 ^ (104 * 2 ^ j) :=
  Nat.pow_le_pow_right (by norm_num) (kseq_le j)

/-- K_j grows strictly with j. -/
theorem Kseq_strictMono : StrictMono Kseq := fun _ _ h =>
  Nat.pow_lt_pow_right (by norm_num) (kseq_strictMono h)

/-- 2^47·K_j ≤ g_j. -/
theorem two_pow_mul_Kseq_le_gseq (j : ℕ) : 2 ^ 47 * Kseq j ≤ gseq j := by
  rw [gseq, Lseq, mul_comm]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- K_j ≤ g_j. -/
theorem Kseq_le_gseq (j : ℕ) : Kseq j ≤ gseq j :=
  le_trans (Nat.le_mul_of_pos_left _ (by positivity)) (two_pow_mul_Kseq_le_gseq j)

/-! ### The top level -/

/-- `gtop` = 3·K_t⁸, the number of nodes of the network of a formula. -/
theorem gtop_eq (s : ℕ) : gtop s = 3 * Ktop s ^ 8 := rfl

/-- Y is the square of `gtop`. -/
theorem Ytop_eq_sq (s : ℕ) : Ytop s = gtop s ^ 2 := rfl

/-- Y = 9·K_t¹⁶. -/
theorem Ytop_eq (s : ℕ) : Ytop s = 9 * Ktop s ^ 16 := by
  rw [Ytop, gtop]; ring

/-- 2^j ≤ k_j: the exponents grow like 104·2^j. -/
theorem two_pow_le_kseq (j : ℕ) : 2 ^ j ≤ kseq j := by
  have h1 := kseq_closed j
  have h2 : j + 1 ≤ 2 ^ j := Nat.lt_two_pow_self
  omega

/-- 2^e ≤ K_t for every e ≤ 2^t, t the number of levels. -/
theorem two_pow_le_Ktop {e s : ℕ} (h : e ≤ 2 ^ depthOf s) : 2 ^ e ≤ Ktop s := by
  rw [Ktop, Kseq]
  exact Nat.pow_le_pow_right (by norm_num) (h.trans (two_pow_le_kseq _))

/-- 2^(52s+692) ≤ K_t (far from sharp: k_t ≥ 94·(⌊19s/3⌋ + 700) + 8). -/
theorem Ktop_lower (s : ℕ) : 2 ^ (52 * s + 692) ≤ Ktop s := by
  have h := kseq_ge (depthOf s)
  rw [Ktop, Kseq]
  refine Nat.pow_le_pow_right (by norm_num) ?_
  unfold depthOf at h ⊢
  omega

/-- K_t is positive. -/
theorem Ktop_pos (s : ℕ) : 0 < Ktop s := Kseq_pos _

/-- C·K_t^e ≤ Y for e ≤ 15 and C ≤ 2^500. -/
theorem mul_Ktop_pow_le_Ytop {C e : ℕ} (hC : C ≤ 2 ^ 500) (he : e ≤ 15) (s : ℕ) : C * Ktop s ^ e ≤ Ytop s := by
  have h1 : 2 ^ 500 ≤ Ktop s := le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) (Ktop_lower s)
  calc C * Ktop s ^ e ≤ Ktop s * Ktop s ^ 15 :=
        Nat.mul_le_mul (hC.trans h1) (Nat.pow_le_pow_right (Ktop_pos s) he)
    _ = Ktop s ^ 16 := by ring
    _ ≤ 9 * Ktop s ^ 16 := Nat.le_mul_of_pos_left _ (by norm_num)
    _ = Ytop s := (Ytop_eq s).symm

/-- K_t ≤ Y. -/
theorem Ktop_le_Ytop (s : ℕ) : Ktop s ≤ Ytop s := by
  have := mul_Ktop_pow_le_Ytop (C := 1) (e := 1) (Nat.one_le_two_pow) (by norm_num) s
  simpa using this

/-- Y is positive. -/
theorem Ytop_pos (s : ℕ) : 0 < Ytop s := lt_of_lt_of_le (Ktop_pos s) (Ktop_le_Ytop s)

/-- 2^(52s+694) ≤ Y (far from sharp, like `Ktop_lower`). -/
theorem Ytop_lower (s : ℕ) : 2 ^ (52 * s + 694) ≤ Ytop s := by
  have h := mul_Ktop_pow_le_Ytop (C := 4) (e := 1) (by norm_num) (by norm_num) s
  calc 2 ^ (52 * s + 694) = 4 * 2 ^ (52 * s + 692) := by rw [show 52 * s + 694 = 52 * s + 692 + 2 by ring, pow_add]; ring
    _ ≤ 4 * Ktop s ^ 1 := by rw [pow_one]; exact Nat.mul_le_mul_left _ (Ktop_lower s)
    _ ≤ Ytop s := h

/-- Y ≤ 2^(2^(t+11)), t the number of levels. -/
theorem Ytop_le (s : ℕ) : Ytop s ≤ 2 ^ 2 ^ (depthOf s + 11) := by
  have h1 : Ktop s ≤ 2 ^ (104 * 2 ^ depthOf s) := Kseq_upper _
  have h2 : 1 ≤ 2 ^ depthOf s := Nat.one_le_two_pow
  calc Ytop s = 9 * Ktop s ^ 16 := Ytop_eq s
    _ ≤ 2 ^ 4 * (2 ^ (104 * 2 ^ depthOf s)) ^ 16 := Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_left h1 16)
    _ = 2 ^ (4 + 104 * 2 ^ depthOf s * 16) := by rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ 2 ^ (depthOf s + 11) := by
      refine Nat.pow_le_pow_right (by norm_num) ?_
      rw [pow_add]
      norm_num
      omega

end PaddedDescent
