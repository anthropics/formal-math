/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GraphProblems.Interfaces

/-! # Corollary 7: reading the input word

The word of a graph is n in unary, possibly s in unary, and the n² entries of the adjacency matrix
row by row. This file shows that `read1` and `read2` recover n, s and the matrix from the word, that
the
matrix has n² entries, and that the entry u·n + v of the matrix says whether u and v are adjacent. -/

public section

namespace GraphProblems

namespace Read

/-- The number of ones at the start of 1ᵐ0x is m. -/
theorem ones_unary_append (m : ℕ) (x : List Bool) : ones (unary m ++ x) = m := by
  induction m with
  | zero => simp [ones, unary]
  | succ m ih =>
    simp only [ones, unary, List.replicate_succ, List.cons_append, List.takeWhile_cons, id, if_true, List.length_cons] at ih ⊢
    rw [ih]

/-- What follows the first ones and the zero that ends them in 1ᵐ0x is x. -/
theorem rest_unary_append (m : ℕ) (x : List Bool) : rest (unary m ++ x) = x := by
  induction m with
  | zero => simp [rest, unary]
  | succ m ih =>
    simp only [rest, unary, List.replicate_succ, List.cons_append, List.dropWhile_cons, id, if_true] at ih ⊢
    exact ih

/-- In a list of rows of length n written one after the other, the entry i·n + j is the entry j of
row i. -/
theorem getD_flatMap {α β : Type} (f : α → List β) (n : ℕ) (d : β) {j : ℕ} (hj : j < n) :
    ∀ (L : List α) (_ : ∀ a ∈ L, (f a).length = n) (i : ℕ), (L.flatMap f).getD (i * n + j) d = (L[i]?.map fun a => (f a).getD j d).getD d
  | [], _, i => by simp
  | a :: L, hL, 0 => by
    have ha : (f a).length = n := hL a (by simp)
    rw [List.flatMap_cons, zero_mul, zero_add, List.getD_append _ _ _ _ (by omega)]
    simp
  | a :: L, hL, i + 1 => by
    have ha : (f a).length = n := hL a (by simp)
    rw [List.flatMap_cons, List.getD_append_right _ _ _ _ (by rw [ha]; nlinarith), ha,
      show (i + 1) * n + j - n = i * n + j by rw [add_mul, one_mul]; omega,
      getD_flatMap f n d hj L (fun b hb => hL b (by simp [hb])) i]
    simp

end Read

open Read

/-- `read1` recovers n and the matrix from the word of a graph. -/
theorem stRead1 : StRead1 := fun n G => by
  rw [read1, code, ones_unary_append, rest_unary_append]

/-- `read2` recovers n, s and the matrix from the word of a graph and a number. -/
theorem stRead2 : StRead2 := fun n G s => by
  rw [read2, codeWith, ones_unary_append, rest_unary_append, ones_unary_append, rest_unary_append]

/-- The entry u·n + v of the matrix is 1 if and only if u and v are adjacent. -/
theorem stAdj : StAdj := fun n G u v => by
  classical
  rw [adjB, matrix, getD_flatMap _ n false v.2 _ (by simp)]
  simp

/-- The matrix has n² entries. -/
theorem stMatrixLength : StMatrixLength := fun n G => by
  simp [matrix, List.length_flatMap]

end GraphProblems
