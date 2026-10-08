/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Machine.Footprint
public import ThreeSumApsp.ModelChecks.Counting
public import ThreeSumApsp.Statements.Agreement
public import Mathlib.Data.List.GetD

/-!
# 3SUM needs linear time on the word RAM

A check of the definition of "solved in time T on the word RAM" (`SolvedInTimeAt`; the model is that
of Section 2): it cannot be met for free.  A program that takes fewer than
`(n - 2) / 2` steps leaves one of the numbers unread (`exec_congr`, `exists_offset_notMem`).  On the
instance 1, -1, 1, 1, …, which has no solution, and on the instance with 0 at the place of the
unread number, which has one, it gives the same verdict.  The same holds for "solved in time
`O(n^r)`" in the sense of `EndStatement.lean` (`not_endStatement_solvedInTime_threeSum`, by
`agreement_solvedInTime`).
-/

@[expose] public section

open ThreeSumApsp.WordRam
open EndStatement (loadWords)

namespace ThreeSumApsp
namespace WordRam

variable {W : ℕ}

/-! ## Two instances of 3SUM that differ in one cell -/

/-- The numbers `1, -1, 1, 1, …`: the second is -1, all others are 1. -/
def oddVec (n : ℕ) (i : Fin n) : ℤ := if (i : ℕ) = 1 then -1 else 1

/-- Each of the numbers `1, -1, 1, 1, …` is 1 or -1. -/
theorem oddVec_eq_or (n : ℕ) (i : Fin n) : oddVec n i = 1 ∨ oddVec n i = -1 := by
  unfold oddVec
  split_ifs <;> simp

/-- The numbers `1, -1, 1, 1, …` are odd, so no three of them sum to 0. -/
theorem not_threeSum_oddVec (n : ℕ) : ¬ ThreeSum (oddVec n) := by
  rintro ⟨i, j, k, -, -, -, h⟩
  rcases oddVec_eq_or n i with hi | hi <;> rcases oddVec_eq_or n j with hj | hj <;>
    rcases oddVec_eq_or n k with hk | hk <;> rw [hi, hj, hk] at h <;> omega

/-- With 0 at a place `p ≥ 2` the numbers `1, -1, 1, 1, …` have a solution: `1 + (-1) + 0 = 0`. -/
theorem threeSum_update_oddVec {n : ℕ} (p : Fin n) (hp : 2 ≤ (p : ℕ)) :
    ThreeSum (Function.update (oddVec n) p 0) := by
  have hn := p.isLt
  have hzero : (⟨0, by omega⟩ : Fin n) ≠ p := Fin.ne_of_val_ne (show 0 ≠ (p : ℕ) by omega)
  have hone : (⟨1, by omega⟩ : Fin n) ≠ p := Fin.ne_of_val_ne (show 1 ≠ (p : ℕ) by omega)
  refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, p, Fin.ne_of_val_ne zero_ne_one, hone, hzero, ?_⟩
  rw [Function.update_of_ne hzero, Function.update_of_ne hone, Function.update_self]
  simp [oddVec]

/-- Numbers of absolute value at most 1 as an instance of 3SUM with the bound `U = n^κ`. -/
def smallInst {n : ℕ} (κ : ℕ) (hn : 1 ≤ n) (x : Fin n → ℤ) (hx : ∀ i, (x i).natAbs ≤ 1) :
    Bounded EndStatement.ThreeSum where
  n := n
  U := n ^ κ
  x := x
  bounded a ha := by
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
    exact (hx i).trans (Nat.one_le_pow _ _ hn)

/-- The numbers `1, -1, 1, 1, …` have absolute value 1. -/
theorem natAbs_oddVec_le (n : ℕ) (i : Fin n) : (oddVec n i).natAbs ≤ 1 := by
  rcases oddVec_eq_or n i with h | h <;> simp [h]

/-- The numbers `1, -1, 1, 1, …` with one of them replaced by 0 have absolute value at most 1. -/
theorem natAbs_update_oddVec_le {n : ℕ} (p i : Fin n) :
    (Function.update (oddVec n) p 0 i).natAbs ≤ 1 := by
  rcases eq_or_ne i p with rfl | h
  · simp
  · rw [Function.update_of_ne h]
    exact natAbs_oddVec_le n i

/-- A change of the number at place `p` changes the starting memory in the cell `1 + p` only. -/
theorem loadWords_update_eq {n : ℕ} (x : Fin n → ℤ) (p : Fin n) (v a : ℤ)
    (ha : a ≠ 1 + ((p : ℕ) : ℤ)) :
    loadWords W ((n : ℤ) :: List.ofFn (Function.update x p v)) a =
      loadWords W ((n : ℤ) :: List.ofFn x) a := by
  rcases lt_or_ge a 0 with h0 | h0
  · rw [WordRam.loadWords_mem_neg _ _ h0, WordRam.loadWords_mem_neg _ _ h0]
  · obtain ⟨b, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    rw [WordRam.loadWords_mem_nat, WordRam.loadWords_mem_nat]
    congr 1
    rcases b with _ | b
    · rfl
    · simp only [List.getD_cons_succ]
      by_cases hb : b < n
      · rw [List.getD_eq_getElem _ _ (by simpa using hb),
          List.getD_eq_getElem _ _ (by simpa using hb), List.getElem_ofFn, List.getElem_ofFn,
          Function.update_of_ne (Fin.ne_of_val_ne fun h : b = (p : ℕ) => ha (by
            push_cast
            omega))]
      · rw [List.getD_eq_default _ _ (by simpa using hb),
          List.getD_eq_default _ _ (by simpa using hb)]

end WordRam

open WordRam

/-- For no exponent `a < 1`, no `e` and no `κ` does a program decide 3SUM in `O(n^a (log n)^e)`
time, because it cannot read its input. -/
theorem not_solvedInTimeAt_threeSum (κ : ℕ) {a : ℝ} (ha : a < 1) (e : ℕ) :
    ¬ SolvedInTimeAt EndStatement.ThreeSum κ a e := by
  intro h
  obtain ⟨P, b, C, hs⟩ := solvedInTimeAt_iff.1 h
  -- a size at which the time bound is far below the number of cells of the input
  obtain ⟨n, hn3, hlt⟩ := exists_sublinear_bound_lt ha e C
  have hn1 : 1 ≤ n := by omega
  -- any admissible word size
  set bits : ℕ := b * (([n].map Nat.log2).sum + 1)
  -- the run on the instance 1, -1, 1, 1, …, which has no solution
  obtain ⟨t, verdict, c, ht, hrun, hans⟩ :=
    hs (smallInst κ hn1 (oddVec n) (natAbs_oddVec_le n)) rfl bits le_rfl
  have hverdict : verdict = false :=
    Bool.eq_false_iff.2 (mt (show verdict = true ↔ ThreeSum (oddVec n) from hans.1).1
      (not_threeSum_oddVec n))
  -- a number from the third on that it does not read
  obtain ⟨R, hR, hcongr⟩ := exec_congr P t ⟨0, _⟩ _ hrun
  have htime : 2 * t + 2 < n := by
    have hreal : (t : ℝ) ≤ C * ((n : ℝ) ^ a * Real.log n ^ e + 1) := ht
    exact_mod_cast (by linarith : 2 * (t : ℝ) + 2 < (n : ℝ))
  obtain ⟨r, hr, hunread⟩ := exists_offset_notMem (n := n - 2) (hR.trans_lt (by omega)) 3
  obtain ⟨p, hp⟩ : ∃ p : Fin n, (p : ℕ) = r + 2 := ⟨⟨r + 2, by omega⟩, rfl⟩
  rw [show (3 : ℤ) + (r : ℤ) = 1 + ((p : ℕ) : ℤ) by rw [hp]; push_cast; ring] at hunread
  -- the run on the instance with 0 at place p gives the same verdict
  obtain ⟨c₂, hrun₂⟩ :=
    hcongr ⟨0, loadWords bits ((n : ℤ) :: List.ofFn (Function.update (oddVec n) p 0))⟩ rfl
      fun a₁ ha₁ => loadWords_update_eq (oddVec n) p 0 a₁ fun h => hunread (h ▸ ha₁)
  -- but that instance has a solution
  obtain ⟨t₂, verdict₂, c₃, -, hrun₃, hans₃⟩ :=
    hs (smallInst κ hn1 _ (natAbs_update_oddVec_le p)) rfl bits le_rfl
  have hverdict₂ : verdict₂ = true :=
    (show verdict₂ = true ↔ ThreeSum (Function.update (oddVec n) p 0) from hans₃.1).2
      (threeSum_update_oddVec p (hp ▸ Nat.le_add_left 2 r))
  have heq := congrArg Prod.fst (exec_unique (c := ⟨0, _⟩) hrun₂ hrun₃)
  simp only [hverdict, hverdict₂] at heq
  exact absurd heq (by decide)

/-- A bound `O(n^r)` of `EndStatement.lean` with a negative exponent `r` is a bound `O(1)`. -/
private theorem bigO_zero_of_neg {T : ℕ → ℕ} {r : ℚ} (hr : r < 0) (h : EndStatement.BigO T r) :
    EndStatement.BigO T 0 := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K, fun n hn => ?_⟩
  have hbound := hK n hn
  rw [Int.toNat_of_nonpos (Rat.num_nonpos.2 hr.le)] at hbound
  simpa using (Nat.le_self_pow r.den_ne_zero (T n)).trans hbound

/-- For no rational exponent `r < 1` does a program decide 3SUM in `O(n^r)` time in the sense of
`EndStatement.lean`, the sense of the five claims. -/
theorem not_endStatement_solvedInTime_threeSum {r : ℚ} (hr : r < 1) :
    ¬ EndStatement.ThreeSum.SolvedInTime r := by
  intro h
  rcases lt_or_ge r 0 with hneg | hr0
  · have hzero : EndStatement.ThreeSum.SolvedInTime 0 := fun κ => by
      obtain ⟨P, b, T, hT, hsolves⟩ := h κ
      exact ⟨P, b, T, bigO_zero_of_neg hneg hT, hsolves⟩
    exact not_solvedInTimeAt_threeSum 0 (by norm_num) 0
      ((agreement_solvedInTime _ 0 le_rfl).1 hzero 0)
  · exact not_solvedInTimeAt_threeSum 0 (by exact_mod_cast hr) 0
      ((agreement_solvedInTime _ r hr0).1 h 0)

end ThreeSumApsp
