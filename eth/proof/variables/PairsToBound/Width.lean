/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PairsToBound.Defs
import SparsificationLemma.StepSparsify
import Mathlib.Tactic.Ring

/-! # The width of Step 6, and the number of clauses

**The sentences answered** (Step 6 of Appendix D). «As in Step 5, k is the largest number of
literals in a clause, or 3 if that is larger, which multiplies k² by at most 9.» «… as there are
fewer than (2n+1)^k ≤ n^(2k) clauses …»

**What is proved.** `widthOr3Stmt : WidthOr3Stmt`: the number `widthOr3 φ` is at least 3; a formula
φ without a repeated clause is a k-CNF for k = `widthOr3 φ`; and if φ is a k-CNF for some k ≥ 1,
then `widthOr3 φ` ≤ max(k, 3) and its square is at most 9k².
`clauseCountPowStmt : ClauseCountPowStmt`: (2n+1)^k ≤ n^(2k) for n ≥ 3.

**How.** `widthOr3 φ` is the largest number in a list, computed from the right with the start value 3.
Three lemmas on such a maximum (it is at least the start value, at least every member, and at most
every common upper bound) give the first statement; max(k, 3) ≤ 3k for k ≥ 1 gives the factor 9.
The second statement is a sentence of Step 5 too and is taken from there
(`SparsificationLemma.StepSparsify.pow_le`). -/

public section

namespace PairsToBound

open Sat3 (CNF)

/-! ### The largest number of a list, with a start value -/

/-- The maximum of a list, computed from the right with the start value a, is at least a. -/
theorem start_le_foldr_max (l : List ℕ) (a : ℕ) : a ≤ l.foldr max a := by
  induction l with
  | nil => exact le_rfl
  | cons b l ih => exact ih.trans (le_max_right _ _)

/-- The maximum of a list, computed from the right with any start value, is at least every member of
the list. -/
theorem mem_le_foldr_max {l : List ℕ} {a x : ℕ} (h : x ∈ l) : x ≤ l.foldr max a := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

/-- A number that is at least the start value and at least every member of the list is at least the
maximum. -/
theorem foldr_max_le {l : List ℕ} {a b : ℕ} (ha : a ≤ b) (h : ∀ x ∈ l, x ≤ b) : l.foldr max a ≤ b := by
  induction l with
  | nil => exact ha
  | cons c l ih =>
    rw [List.foldr_cons]
    exact max_le (h c List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

/-! ### The width -/

/-- The width of Step 6 is at least 3. -/
theorem three_le_widthOr3 {n : ℕ} (φ : CNF n) : 3 ≤ widthOr3 φ := start_le_foldr_max _ 3

/-- No clause has more literals than the width of Step 6. -/
theorem length_le_widthOr3 {n : ℕ} {φ : CNF n} {C : List (Sat3.Lit n)} (h : C ∈ φ) : C.length ≤ widthOr3 φ :=
  mem_le_foldr_max (List.mem_map_of_mem h)

/-- If no clause of φ has more than k literals, the width of Step 6 is at most max(k, 3). -/
theorem widthOr3_le_max {n k : ℕ} {φ : CNF n} (h : ∀ C ∈ φ, C.length ≤ k) : widthOr3 φ ≤ max k 3 := by
  refine foldr_max_le (le_max_right _ _) fun x hx => ?_
  obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hx
  exact (h C hC).trans (le_max_left _ _)

/-- «k is the largest number of literals in a clause, or 3 if that is larger, which multiplies k² by
at most 9.» -/
theorem widthOr3Stmt : WidthOr3Stmt := by
  intro n φ
  refine ⟨three_le_widthOr3 φ, fun hnd => ⟨fun C hC => length_le_widthOr3 hC, hnd⟩, fun k hk hφ => ?_⟩
  have h1 : widthOr3 φ ≤ max k 3 := widthOr3_le_max hφ.1
  have h2 : widthOr3 φ ≤ 3 * k := h1.trans (max_le (by omega) (by omega))
  refine ⟨h1, ?_⟩
  calc widthOr3 φ ^ 2 ≤ (3 * k) ^ 2 := Nat.pow_le_pow_left h2 2
    _ = 9 * k ^ 2 := by ring

/-! ### The number of clauses -/

/-- «(2n+1)^k ≤ n^(2k)», for n ≥ 3. -/
theorem clauseCountPowStmt : ClauseCountPowStmt := fun k _ hn => SparsificationLemma.StepSparsify.pow_le hn k

end PairsToBound
