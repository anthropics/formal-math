/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaperStatements
public import ThreeSumApsp.Lang.Lib.Seg

/-!
# Reading the trusted layout

Matrices are written row by row (`rowMajor`), and an input is a concatenation of lists.  This file
says which number is in which cell (`getD_rowMajor`, `seg_memOf`, `matAt_of_seg`).
-/

public section

namespace Light

open ThreeSumApsp ThreeSumApsp.WordRam

private theorem rowMajor_succ {n m : ℕ} (A : Fin (n + 1) → Fin m → ℤ) :
    rowMajor A = (List.finRange m).map (A 0) ++ rowMajor fun i : Fin n => A i.succ := by
  simp [rowMajor, List.finRange_succ, List.flatMap_map]

theorem length_rowMajor : ∀ {n m : ℕ} (A : Fin n → Fin m → ℤ), (rowMajor A).length = n * m
  | 0, m, A => by simp [rowMajor]
  | n + 1, m, A => by
    rw [rowMajor_succ, List.length_append, length_rowMajor, List.length_map, List.length_finRange]
    ring

/-- The entry `(i, j)` of an `n × m` matrix is at place `i m + j`. -/
theorem getD_rowMajor : ∀ {n m : ℕ} (A : Fin n → Fin m → ℤ) (i : Fin n) (j : Fin m),
    (rowMajor A).getD ((i : ℕ) * m + (j : ℕ)) 0 = A i j
  | 0, _, _, i, _ => i.elim0
  | n + 1, m, A, i, j => by
    rw [rowMajor_succ]
    refine Fin.cases ?_ (fun i' => ?_) i
    · rw [Fin.val_zero, Nat.zero_mul, Nat.zero_add, List.getD_append _ _ _ _ (by simp)]
      simp [List.getD_eq_getElem?_getD]
    · rw [List.getD_append_right _ _ _ _ (by simp [Fin.val_succ, Nat.add_mul]; omega)]
      have : ((i'.succ : Fin (n + 1)) : ℕ) * m + (j : ℕ) - ((List.finRange m).map (A 0)).length =
          (i' : ℕ) * m + (j : ℕ) := by
        simp [Fin.val_succ, Nat.add_mul]
        omega
      rw [this]
      exact getD_rowMajor (fun i : Fin n => A i.succ) i' j

theorem mem_rowMajor {n m : ℕ} {A : Fin n → Fin m → ℤ} {x : ℤ} (h : x ∈ rowMajor A) :
    ∃ i j, A i j = x := by
  simp only [rowMajor, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and] at h
  exact h

/-- Every entry of a matrix stands in the list of its rows. -/
theorem mem_rowMajor_self {n m : ℕ} (A : Fin n → Fin m → ℤ) (i : Fin n) (j : Fin m) :
    A i j ∈ rowMajor A := by
  simp only [rowMajor, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
  exact ⟨i, j, rfl⟩

/-- A cell in the first part of a concatenation. -/
theorem memOf_append_left {l₁ : List ℤ} (l₂ : List ℤ) {a : ℕ} (h : a < l₁.length) :
    memOf (l₁ ++ l₂) a = memOf l₁ a := by
  unfold memOf
  rw [List.getD_append _ _ _ _ h]

/-- A cell after the first part of a concatenation. -/
theorem memOf_append_right (l₁ l₂ : List ℤ) (a : ℕ) :
    memOf (l₁ ++ l₂) (l₁.length + a) = memOf l₂ a := by
  unfold memOf
  rw [List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left]

/-- A part of a concatenation is a segment of the memory. -/
theorem seg_memOf (l₁ l l₂ : List ℤ) : Seg (memOf (l₁ ++ l ++ l₂)) l₁.length l := by
  intro i hi
  rw [List.append_assoc, memOf_append_right, memOf_append_left _ hi]
  exact List.getD_eq_getElem _ _ hi

/-- The first of two lists after the size. -/
theorem seg_first (n : ℤ) (l₁ l₂ : List ℤ) : Seg (memOf (n :: (l₁ ++ l₂))) 1 l₁ := by
  simpa using seg_memOf [n] l₁ l₂

/-- The second of two lists after the size. -/
theorem seg_second (n : ℤ) (l₁ l₂ : List ℤ) :
    Seg (memOf (n :: (l₁ ++ l₂))) (1 + l₁.length) l₂ := by
  have := seg_memOf (n :: l₁) l₂ []
  simpa [Nat.add_comm] using this

/-- A matrix written row by row. -/
theorem matAt_of_seg {n k : ℕ} {μ : ℕ → ℤ} {a : ℕ} {A : Matrix (Fin n) (Fin k) ℤ}
    (h : Seg μ a (rowMajor A)) : MatAt μ a A := by
  intro i j
  have hlt : (i : ℕ) * k + (j : ℕ) < (rowMajor A).length :=
    (Nat.mul_add_lt_mul i.isLt j.isLt).trans_eq (length_rowMajor _).symm
  rw [Nat.add_assoc, h _ hlt, ← List.getD_eq_getElem _ 0 hlt]
  exact getD_rowMajor A i j

/-- A square matrix written row by row: the two definitions agree. -/
theorem rowByRow_eq {n : ℕ} (w : Fin n → Fin n → ℤ) : EndStatement.rowByRow w = rowMajor w := by
  simp [EndStatement.rowByRow, rowMajor, List.ofFn_eq_map, List.flatMap_def]

end Light
