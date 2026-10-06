/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Spec.Sec2.Theorem5.Subsets
public import Mathlib.Algebra.Order.Ring.Int

/-!
# The table of subsets: how a row is made from the row before it

Section 2.3.4: "We fix K₀² ≤ K distinct subsets of {1, …, L} of size m, one for each block product
of the grid, the same in every tile."  The programs keep them in a table.  Row number `s` of the
table is the mask `Spec.unrank L m s`, as `L` cells 1 and 0 (`bit`).  No program occurs here.

* The first row is `m` ones followed by zeros (`bit_unrank_zero`).
* Two consecutive masks are `pre 1 0 0^a 1^b` and `pre 0 1 1^b 0^a` (`Spec.unrank_succ_shape`).  So
  one pass from the end of the old row finds `b` and the length of `pre`: `scanAt` is the state of
  this scan after a number of rounds, and `scanAt_shape` is what it has found after all rounds.
* A second pass writes the new row: `newCell` is the cell that it writes (`bit_unrank_succ`), and
  the numbers that it computes on the way are small (`scanAt_fits`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec.Subsets

/-- A truth value as a cell. -/
def bit (b : Bool) : ℤ := if b then 1 else 0

/-- Row 0 of the table is `m` ones followed by `L - m` zeros. -/
theorem bit_unrank_zero {L m q : ℕ} (hm : m ≤ L) (hq : q < L) :
    bit ((Spec.unrank L m 0).getD q false) = if q < m then 1 else 0 := by
  rw [Spec.unrank_zero hm]
  grind [bit]

/-- The entries of a list of the form `pre ++ x :: y :: (u^a ++ v^b)`. -/
private theorem getD_shape (pre : List Bool) (x y u v : Bool) (a b q : ℕ) :
    (pre ++ x :: y :: (List.replicate a u ++ List.replicate b v)).getD q false =
      if q < pre.length then pre.getD q false
      else if q = pre.length then x
      else if q = pre.length + 1 then y
      else if q < pre.length + 2 + a then u
      else if q < pre.length + 2 + a + b then v else false := by
  grind

/-! ## The backward scan -/

/-- The state of the scan: the phase (0 while the ones at the end of the row are counted, 1 while
the zeros before them are passed, 2 when the 1 before these zeros has been found), the number of
ones at the end of the row, and the position of the 1 that was found.  The three fields are the
contents of three local variables of the routine, so they are integers, and `scanStep` and `newCell`
compare them by `<`, the comparison of the language. -/
structure Scan where
  /-- The phase: 0, 1 or 2. -/
  phase : ℤ
  /-- The number of ones at the end of the row. -/
  ones : ℤ
  /-- The position of the last 1 that is followed by a 0. -/
  pos : ℤ

/-- The result of a scan fits into a row of `L` cells: the position `p` and the number `b` of ones
are natural numbers with `p + 2 + b ≤ L`. -/
def Scan.Fits (S : Scan) (L : ℕ) : Prop := 0 ≤ S.pos ∧ 0 ≤ S.ones ∧ S.pos + 2 + S.ones ≤ L

/-- One round of the scan: `x` is the cell that is read, and `q` its position. -/
def scanStep (x q : ℤ) (S : Scan) : Scan :=
  if S.phase < 1 then (if x < 1 then { S with phase := 1 } else { S with ones := S.ones + 1 })
  else if S.phase < 2 then (if x < 1 then S else { S with phase := 2, pos := q })
  else S

/-- The state of the scan of a row of length `L` after `j` rounds. -/
def scanAt (row : ℕ → ℤ) (L : ℕ) : ℕ → Scan
  | 0 => ⟨0, 0, 0⟩
  | j + 1 => scanStep (row (L - 1 - j)) ((L : ℤ) - 1 - (j : ℤ)) (scanAt row L j)

/-- One round counts at most one more 1. -/
private theorem scanStep_ones (x q : ℤ) (S : Scan) :
    (scanStep x q S).ones = S.ones ∨ (scanStep x q S).ones = S.ones + 1 := by
  unfold scanStep
  split_ifs <;> simp

/-- After `j` rounds at most `j` ones have been counted. -/
theorem scanAt_ones_le (row : ℕ → ℤ) (L j : ℕ) :
    0 ≤ (scanAt row L j).ones ∧ (scanAt row L j).ones ≤ j := by
  induction j with
  | zero => simp [scanAt]
  | succ j ih =>
    have hstep := scanStep_ones (row (L - 1 - j)) ((L : ℤ) - 1 - (j : ℤ)) (scanAt row L j)
    rw [scanAt]
    push_cast
    omega

section shape
variable {pre : List Bool} {a b L : ℕ} {row : ℕ → ℤ} (hL : L = pre.length + 2 + a + b)
  (hrow : ∀ q < L, row q =
    bit ((pre ++ true :: false :: (List.replicate a false ++ List.replicate b true)).getD q false))
include hL hrow

/-- The cell that round `j` reads: 1 for the `b` ones at the end of the row, 0 for the `a + 1` zeros
before them, and 1 for the cell before these. -/
private theorem row_sub (j : ℕ) (hj : j ≤ b + a + 1) :
    row (L - 1 - j) = if j < b then 1 else if j < b + a + 1 then 0 else 1 := by
  rw [hrow _ (by omega), getD_shape]
  grind [bit]

/-- Phase 0: the `b` ones at the end of the row are counted. -/
private theorem scanAt_count (j : ℕ) (hj : j ≤ b) : scanAt row L j = ⟨0, j, 0⟩ := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [scanAt, ih (by omega), row_sub hL hrow j (by omega), if_pos (by omega)]
    simp [scanStep]

/-- Phase 1: the `a + 1` zeros before the ones are passed. -/
private theorem scanAt_pass (i : ℕ) (hi : i ≤ a) : scanAt row L (b + 1 + i) = ⟨1, b, 0⟩ := by
  induction i with
  | zero =>
    rw [Nat.add_zero, scanAt, scanAt_count hL hrow b le_rfl, row_sub hL hrow b (by omega),
      if_neg (by omega), if_pos (by omega)]
    simp [scanStep]
  | succ i ih =>
    rw [← Nat.add_assoc, scanAt, ih (by omega), row_sub hL hrow _ (by omega), if_neg (by omega),
      if_pos (by omega)]
    simp [scanStep]

/-- Phase 2: the 1 before the `a + 1` zeros is found, at the position after `pre`, and from then on
the state stays as it is. -/
private theorem scanAt_found (i : ℕ) (hi : i ≤ pre.length) :
    scanAt row L (b + 1 + a + 1 + i) = ⟨2, b, pre.length⟩ := by
  induction i with
  | zero =>
    rw [Nat.add_zero, scanAt, scanAt_pass hL hrow a le_rfl, row_sub hL hrow _ (by omega),
      if_neg (by omega), if_neg (by omega),
      show (L : ℤ) - 1 - ((b + 1 + a : ℕ) : ℤ) = pre.length by omega]
    simp [scanStep]
  | succ i ih =>
    rw [← Nat.add_assoc, scanAt, ih (by omega)]
    rfl

/-- The scan of a row of the shape `pre 1 0 0^a 1^b` finds `b` and the length of `pre`. -/
private theorem scanAt_shape : scanAt row L L = ⟨2, b, pre.length⟩ := by
  rw [← scanAt_found hL hrow pre.length le_rfl]
  congr 1
  omega

end shape

/-! ## The writing pass -/

/-- The cell number `q` of the new row, from the cell of the old row and the result of the scan. -/
def newCell (S : Scan) (old q : ℤ) : ℤ :=
  if q < S.pos then old else if q < S.pos + 1 then 0 else if q < S.pos + 2 + S.ones then 1 else 0

section next
variable {L m s : ℕ} (hs : s + 1 < L.choose m) {row : ℕ → ℤ}
  (hrow : ∀ q < L, row q = bit ((Spec.unrank L m s).getD q false))
include hs hrow

/-- **From one row to the next.**  If row number `s` has a successor, the cells of row `s + 1` are
given by `newCell`, from the cells of row `s` and the result of its scan. -/
theorem bit_unrank_succ {q : ℕ} (hq : q < L) :
    bit ((Spec.unrank L m (s + 1)).getD q false) = newCell (scanAt row L L) (row q) q := by
  obtain ⟨pre, a, b, hL, hthis, hnext⟩ := Spec.unrank_succ_shape hs
  rw [hthis] at hrow
  rw [scanAt_shape hL hrow, hrow q hq, hnext, getD_shape, getD_shape, newCell]
  dsimp only
  split_ifs <;> first | rfl | (exfalso; omega)

/-- The result of the scan of a row that has a successor fits into a row. -/
theorem scanAt_fits : (scanAt row L L).Fits L := by
  obtain ⟨pre, a, b, hL, hthis, -⟩ := Spec.unrank_succ_shape hs
  rw [hthis] at hrow
  rw [scanAt_shape hL hrow, Scan.Fits]
  dsimp only
  omega

end next

end ThreeSumApsp.Spec.Subsets
