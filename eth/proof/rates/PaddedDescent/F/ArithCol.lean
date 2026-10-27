/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.Seq
public import PaddedDescent.F.Prog
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! # The grid is large enough for the colouring, at every level

The colouring lemma of this development, which splits g nodes into K groups (colours) for the
balancing step (compare Lemma 8, whose condition differs), with relative error 1/D, asks for a
number m with 4·D²·m·K ≤ g and (g+2)·K < 2^m (`ColOK K g`). Here:
for K = K_j, g = g_j = K_j·2^(47+j) and D = `Dcol` = 2^18 the number m = 2^(9+j) will do, at every
level j. -/

public section

namespace PaddedDescent.F.Arith

open PaddedDescent

/-- 4·D²·2^(9+j)·K_j = g_j. -/
theorem four_mul_Dcol_sq_mul (j : ℕ) : 4 * Dcol ^ 2 * 2 ^ (9 + j) * Kseq j = gseq j := by
  rw [gseq, Lseq, Dcol, show 47 + j = 38 + (9 + j) by omega, pow_add 2 38]
  ring

/-- (g_j + 2)·K_j < 2^(2^(9+j)). -/
theorem gseq_add_two_mul_lt (j : ℕ) : (gseq j + 2) * Kseq j < 2 ^ 2 ^ (9 + j) := by
  have h1 := kseq_closed j
  have h2 : 2 ≤ gseq j := le_trans (by norm_num) ((Kseq_ge j).trans (Kseq_le_gseq j))
  have h3 : (2 : ℕ) ^ (9 + j) = 512 * 2 ^ j := by rw [pow_add]; norm_num
  calc (gseq j + 2) * Kseq j ≤ (2 * gseq j) * Kseq j := Nat.mul_le_mul_right _ (by omega)
    _ = 2 ^ (1 + (kseq j + 47 + j) + kseq j) := by rw [gseq_eq, Kseq]; ring
    _ < 2 ^ 2 ^ (9 + j) := Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- The hypothesis of the colouring lemma holds for (K_j, g_j). -/
theorem colOK_seq (j : ℕ) : ColOK (Kseq j) (gseq j) :=
  ⟨2 ^ (9 + j), (four_mul_Dcol_sq_mul j).le, gseq_add_two_mul_lt j⟩

end PaddedDescent.F.Arith
