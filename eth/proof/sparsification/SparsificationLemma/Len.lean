/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsificationLemma.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # The number of clauses of a k-CNF in which every variable occurs in few clauses

This file proves `StLenOfOcc`, with the list lemma `length_le_sum_countP`: a k-CNF on n variables in
which every variable occurs in at most Δ clauses has at most Δ·n clauses.
`StLenOfOcc`: every clause has a variable v < n, so it is counted in the number of occurrences of at
least one v < n. Hence the number of clauses is at most the sum of these n numbers, each of which is
at most Δ. -/

public section

namespace SparsificationLemma

open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate UniformInK
open PaddedDescent.F.Mark (occ)

/-- If every member of a list has one of the properties p 0, …, p (n−1), the length of the list is
at most the sum over v < n of the number of members with the property p v. -/
theorem length_le_sum_countP {α : Type} (n : ℕ) (p : ℕ → α → Bool) (L : List α) (h : ∀ a ∈ L, ∃ v < n, p v a = true) :
    L.length ≤ ∑ v ∈ range n, L.countP (p v) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    obtain ⟨v, hv, hp⟩ := h a (List.mem_cons_self ..)
    have h1 : 1 ≤ ∑ w ∈ range n, (if p w a = true then 1 else 0) :=
      le_trans (by simp [hp]) (single_le_sum (f := fun w => if p w a = true then 1 else 0) (fun _ _ => Nat.zero_le _) (mem_range.2 hv))
    have h2 := ih fun b hb => h b (List.mem_cons_of_mem _ hb)
    simp only [List.countP_cons, sum_add_distrib, List.length_cons]
    omega

/-- A k-CNF on n variables in which every variable occurs in at most Δ clauses has at most Δ·n
clauses. -/
theorem stLenOfOcc : StLenOfOcc := by
  intro k n Δ Φ hΦ hocc
  have h1 : Φ.length ≤ ∑ v ∈ range n, Φ.countP (fun C => C.any fun l => l.1 == v) := by
    refine length_le_sum_countP n (fun v C => C.any fun l => l.1 == v) Φ fun C hC => ?_
    obtain ⟨hne, -, hlt⟩ := hΦ C hC
    obtain ⟨l, hl⟩ := List.exists_mem_of_ne_nil C hne
    exact ⟨l.1, hlt l hl, List.any_eq_true.2 ⟨l, hl, by simp⟩⟩
  have h2 : ∑ v ∈ range n, Φ.countP (fun C => C.any fun l => l.1 == v) ≤ ∑ _v ∈ range n, Δ := by
    refine sum_le_sum fun v _ => ?_
    have := hocc v
    rwa [occN, occ, ← List.countP_eq_length_filter] at this
  rw [sum_const, card_range, smul_eq_mul, Nat.mul_comm] at h2
  exact h1.trans h2

end SparsificationLemma
