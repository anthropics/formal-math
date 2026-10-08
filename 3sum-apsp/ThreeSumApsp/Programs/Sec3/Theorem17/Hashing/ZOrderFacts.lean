/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Lib.Seg
public import ThreeSumApsp.Spec.Sec3.Theorem17.ZOrder
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# The table of `spread`: small facts

`spread i` is the number whose digits in base 4 are the binary digits of i; the place of the entry
(a, c) of a matrix in Z-order is 2 spread a + spread c.  The routines that write matrices in Z-order
and the routine that reads the count off their product look `spread` up in a table,
`spreadList n`, the list of spread 0, …, spread (n - 1).  Here are the facts on the table that both
use: a bound on its entries, how it grows, and what a cell of it holds.
-/

public section

namespace Light.Sec3

open ThreeSumApsp ThreeSumApsp.Spec

/-- The number whose digits in base 4 are the binary digits of i is at most i². -/
theorem spread_le_sq (i : ℕ) : spread i ≤ i * i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [spread_zero]
    · have h := ih (i / 2) (by omega)
      rw [spread_eq]
      obtain ⟨q, b, hb, rfl⟩ : ∃ q b, b < 2 ∧ i = 2 * q + b :=
        ⟨i / 2, i % 2, Nat.mod_lt _ (by norm_num), by omega⟩
      rw [show (2 * q + b) / 2 = q by omega] at h ⊢
      rw [show (2 * q + b) % 2 = b by omega]
      nlinarith

theorem spreadList_succ (i : ℕ) : spreadList (i + 1) = spreadList i ++ [((spread i : ℕ) : ℤ)] := by
  simp [spreadList, List.range_succ]

theorem length_spreadList (i : ℕ) : (spreadList i).length = i := by simp [spreadList]

/-- A cell of the table. -/
theorem seg_spreadList_get {μ : ℕ → ℤ} {a n i : ℕ} (h : Seg μ a (spreadList n)) (hi : i < n) :
    μ (a + i) = (spread i : ℕ) := by
  have := h i (by rw [length_spreadList]; exact hi)
  simpa [spreadList] using this

end Light.Sec3
