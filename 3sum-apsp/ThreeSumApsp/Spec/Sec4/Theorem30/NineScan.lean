/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Spec.Sec4.Theorem30.NineStrings
public import ThreeSumApsp.Util.List
public import Mathlib.Data.List.GetD

/-!
# The successor of a string, as two passes from left to right

`nineNext`, which goes from a string with a bounded number of nines to the next one, is defined by
recursion on the string.  A machine goes through the cells of a buffer from left to right.  This
file gives the function in that shape.

* One pass over the string finds the last position whose digit can be raised, and the number of
  nines before it (`nineScan`).
* A second pass writes the next string: the digits before that position are kept, its digit is
  raised by one, and the rest is filled with zeros followed by nines (`raiseAt`).

The result is `nineNext_eq_scan`.  It is proved in two steps: `nineNext` raises the last position
that can be raised (`raisePos`, `nineNext_eq_raise`), and the scan finds that position
(`nineScanFrom_eq`).  For the routine there are, besides, an invariant of the scan
(`nineScan_inv`) and the fact that the filling fits behind the position that is raised
(`raise_fits`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## The last position that can be raised -/

/-- Whether the digit d can be raised when c nines come before it and at most hi nines are
allowed. -/
def canRaise (hi c d : ℕ) : Bool := decide (d < 8) || (decide (d = 8) && decide (c < hi))

/-- The last position of the string whose digit can be raised, with the number of nines before it;
c nines come before the string. -/
private def raisePos (hi : ℕ) : ℕ → List ℕ → Option (ℕ × ℕ)
  | _, [] => none
  | c, d :: l =>
    match raisePos hi (if d = 9 then c + 1 else c) l with
    | some (p, c') => some (p + 1, c')
    | none => if canRaise hi c d then some (0, c) else none

/-- The string with the digit at position p raised by one and the least admissible filling behind
it; c nines come before p. -/
def raiseAt (lo p c : ℕ) (l : List ℕ) : List ℕ :=
  l.take p ++ (l.getD p 0 + 1) ::
    nineFirst (l.length - p - 1) (lo - c - if l.getD p 0 = 8 then 1 else 0)

/-- A digit that can be raised is at most 8. -/
theorem le_of_canRaise {hi c d : ℕ} (h : canRaise hi c d = true) : d ≤ 8 := by
  simp only [canRaise, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h
  omega

/-- What `nineNext` does to the first digit when the rest of the string cannot be raised. -/
private theorem raise_head (lo hi c d : ℕ) (l : List ℕ) :
    nineRaise (lo - c) (hi - c) l.length d
      = (if canRaise hi c d then some (0, c) else none).map
          fun q : ℕ × ℕ => raiseAt lo q.1 q.2 (d :: l) := by
  rw [nineRaise]
  by_cases h8 : d < 8
  · simp [canRaise, h8, raiseAt, Nat.ne_of_lt h8]
  · by_cases h : d = 8 ∧ c < hi
    · simp [canRaise, h.1, h.2, raiseAt]
    · have hcan : canRaise hi c d = false := by
        simp only [canRaise, Bool.or_eq_false_iff, decide_eq_false_iff_not, Bool.and_eq_false_iff]
        exact ⟨h8, by tauto⟩
      rw [if_neg h8, if_neg fun h' => h ⟨h'.1, by omega⟩, hcan]
      rfl

/-- `nineNext` raises the last position that can be raised. -/
private theorem nineNext_eq_raise (lo hi c : ℕ) (l : List ℕ) :
    nineNext (lo - c) (hi - c) l = (raisePos hi c l).map fun q => raiseAt lo q.1 q.2 l := by
  induction l generalizing c with
  | nil => rfl
  | cons d l ih =>
    have hlo : (if d = 9 then lo - c - 1 else lo - c) = lo - (if d = 9 then c + 1 else c) := by
      split_ifs <;> omega
    have hhi : (if d = 9 then hi - c - 1 else hi - c) = hi - (if d = 9 then c + 1 else c) := by
      split_ifs <;> omega
    rw [nineNext, raisePos, hlo, hhi, ih]
    rcases raisePos hi (if d = 9 then c + 1 else c) l with _ | ⟨p, c'⟩
    · exact raise_head lo hi c d l
    · simp [raiseAt]

/-! ## The scan from left to right -/

/-- The state of the scan: 1 if a position that can be raised has been seen, the last such
position, the number of nines before it, and the number of nines seen so far. -/
structure NineScan where
  found : ℕ
  pos : ℕ
  before : ℕ
  nines : ℕ

/-- One step of the scan: the cell number i holds the digit d. -/
def nineScanStep (hi i d : ℕ) (s : NineScan) : NineScan :=
  { found := if canRaise hi s.nines d then 1 else s.found
    pos := if canRaise hi s.nines d then i else s.pos
    before := if canRaise hi s.nines d then s.nines else s.before
    nines := if d = 9 then s.nines + 1 else s.nines }

/-- The scan of a list whose first cell has the number i. -/
def nineScanFrom (hi : ℕ) : ℕ → List ℕ → NineScan → NineScan
  | _, [], s => s
  | i, d :: l, s => nineScanFrom hi (i + 1) l (nineScanStep hi i d s)

/-- The state after the first j cells. -/
def nineScan (hi : ℕ) (l : List ℕ) (j : ℕ) : NineScan := nineScanFrom hi 0 (l.take j) ⟨0, 0, 0, 0⟩

/-- The scan of two lists one after the other: the second list is scanned from the state after the
first. -/
private theorem nineScanFrom_append (hi i : ℕ) (l l' : List ℕ) (s : NineScan) :
    nineScanFrom hi i (l ++ l') s = nineScanFrom hi (i + l.length) l' (nineScanFrom hi i l s) := by
  induction l generalizing i s with
  | nil => rfl
  | cons d l ih =>
    rw [List.cons_append, nineScanFrom, nineScanFrom, ih, List.length_cons]
    congr 1
    omega

/-- The state after one more cell is one step of the scan from the state before that cell. -/
theorem nineScan_succ (hi : ℕ) (l : List ℕ) {j : ℕ} (hj : j < l.length) :
    nineScan hi l (j + 1) = nineScanStep hi j (l.getD j 0) (nineScan hi l j) := by
  rw [nineScan, nineScan, List.take_succ_getD l hj 0, nineScanFrom_append, List.length_take,
    Nat.min_eq_left hj.le, Nat.zero_add]
  rfl

/-- The scan finds the last position that can be raised. -/
private theorem nineScanFrom_eq (hi i : ℕ) (l : List ℕ) (s : NineScan) :
    nineScanFrom hi i l s =
      match raisePos hi s.nines l with
      | some (p, c) => ⟨1, i + p, c, s.nines + l.count 9⟩
      | none => ⟨s.found, s.pos, s.before, s.nines + l.count 9⟩ := by
  induction l generalizing i s with
  | nil => rfl
  | cons d l ih =>
    have hn : (nineScanStep hi i d s).nines = if d = 9 then s.nines + 1 else s.nines := rfl
    have hcount : (if d = 9 then s.nines + 1 else s.nines) + l.count 9
        = s.nines + (d :: l).count 9 := by
      by_cases h : d = 9
      · rw [h, if_pos rfl, List.count_cons_self]
        omega
      · rw [if_neg h, List.count_cons_of_ne h]
    rw [nineScanFrom, ih, raisePos, hn, hcount]
    rcases raisePos hi (if d = 9 then s.nines + 1 else s.nines) l with _ | ⟨p, c⟩
    · by_cases hc : canRaise hi s.nines d <;> simp [nineScanStep, hc]
    · simp only [NineScan.mk.injEq, true_and, and_true]
      omega

/-- **The successor by two passes.**  After the scan of the whole string, either no position can be
raised and the string is the last one, or the next string is obtained by raising the position
found. -/
theorem nineNext_eq_scan (lo hi : ℕ) (l : List ℕ) :
    nineNext lo hi l =
      if (nineScan hi l l.length).found = 1 then
        some (raiseAt lo (nineScan hi l l.length).pos (nineScan hi l l.length).before l)
      else none := by
  have h := nineNext_eq_raise lo hi 0 l
  rw [Nat.sub_zero, Nat.sub_zero] at h
  rw [h, nineScan, List.take_length, nineScanFrom_eq]
  rcases raisePos hi 0 l with _ | ⟨p, c⟩ <;> simp

/-! ## What the scan has found -/

/-- What holds of the state s of the scan after j cells: the counter holds the number of nines
among them, and the position found, if any, is one of them, can be raised, and has the recorded
number of nines before it. -/
structure NineScanInv (hi : ℕ) (l : List ℕ) (j : ℕ) (s : NineScan) : Prop where
  nines : s.nines = (l.take j).count 9
  found : s.found = 0 ∨ s.found = 1
  pos_lt : s.found = 1 → s.pos < j
  canRaise : s.found = 1 → canRaise hi s.before (l.getD s.pos 0) = true
  before : s.found = 1 → s.before = (l.take s.pos).count 9

theorem nineScan_inv (hi : ℕ) (l : List ℕ) {j : ℕ} (hj : j ≤ l.length) :
    NineScanInv hi l j (nineScan hi l j) := by
  induction j with
  | zero => exact ⟨rfl, Or.inl rfl, nofun, nofun, nofun⟩
  | succ j ih =>
    have ih := ih (Nat.le_of_succ_le hj)
    rw [nineScan_succ hi l hj]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [nineScanStep]
    · rw [List.count_take_succ_getD l 9 hj 0, ← ih.nines]
      split_ifs <;> rfl
    · split_ifs
      · exact Or.inr rfl
      · exact ih.found
    · split_ifs
      · exact fun _ => Nat.lt_succ_self j
      · exact fun hf => (ih.pos_lt hf).trans (Nat.lt_succ_self j)
    · split_ifs with hc
      · exact fun _ => hc
      · exact ih.canRaise
    · split_ifs
      · exact fun _ => ih.nines
      · exact ih.before

/-! ## The filling fits -/

/-- Behind a position that can be raised there is room for the nines that are still needed. -/
theorem raise_fits {lo p : ℕ} {l : List ℕ} (hp : p < l.length) (h8 : l.getD p 0 ≤ 8)
    (hlo : lo ≤ l.count 9) : lo - (l.take p).count 9 ≤ l.length - p - 1 := by
  have hsplit : l.count 9 = (l.take p).count 9 + (l.drop p).count 9 := by
    rw [← List.count_append, List.take_append_drop]
  have hdrop : (l.drop p).count 9 = (l.drop (p + 1)).count 9 := by
    rw [List.drop_eq_getElem_cons hp, List.count_cons_of_ne]
    rw [List.getD_eq_getElem _ _ hp] at h8
    omega
  have hle := List.count_le_length (a := 9) (l := l.drop (p + 1))
  rw [List.length_drop] at hle
  omega

end ThreeSumApsp.Spec
