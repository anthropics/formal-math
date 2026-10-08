/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Ring

/-!
# Few indices are far above the average

Let `f` be a function with natural numbers as values on a nonempty finite set `Q`.  Division is
avoided: "`f p` is at most `k` times the average of `f`" is written
`f p * |Q| ≤ k * ∑ p' ∈ Q, f p'`.

* Fewer than `|Q|/k` indices are more than `k` times as bad as the average
  (`Finset.mul_card_above_average_lt`, Markov's inequality).
* So for `k` functions there is one index at which each of them is at most `k` times its average
  (`Finset.exists_forall_mul_card_le_mul_sum`, the union bound).
-/

public section

namespace Finset

/-- Markov's inequality: fewer than `|Q|/k` indices are more than `k` times as bad as the
average. -/
theorem mul_card_above_average_lt {ι : Type*} {Q : Finset ι} (hQ : Q.Nonempty) (k : ℕ)
    (f : ι → ℕ) : k * #{p ∈ Q | k * ∑ p' ∈ Q, f p' < f p * #Q} < #Q := by
  set B := {p ∈ Q | k * ∑ p' ∈ Q, f p' < f p * #Q}
  rcases B.eq_empty_or_nonempty with he | hne
  · rw [he, card_empty, mul_zero]
    exact hQ.card_pos
  refine lt_of_mul_lt_mul_right (a := ∑ p ∈ Q, f p) ?_ (Nat.zero_le _)
  calc k * #B * ∑ p ∈ Q, f p = ∑ _p ∈ B, k * ∑ p' ∈ Q, f p' := by
        rw [sum_const, smul_eq_mul]; ring
    _ < ∑ p ∈ B, f p * #Q := sum_lt_sum_of_nonempty hne fun p hp => (mem_filter.mp hp).2
    _ ≤ ∑ p ∈ Q, f p * #Q := sum_le_sum_of_subset (filter_subset _ _)
    _ = #Q * ∑ p ∈ Q, f p := by rw [← sum_mul, mul_comm]

/-- The union bound: one index is good for `k` functions at once, in that each function is at most
`k` times its average there. -/
theorem exists_forall_mul_card_le_mul_sum {ι : Type*} {Q : Finset ι} (hQ : Q.Nonempty) (k : ℕ)
    (f : Fin k → ι → ℕ) : ∃ p ∈ Q, ∀ i, f i p * #Q ≤ k * ∑ p' ∈ Q, f i p' := by
  classical
  by_contra hcon
  push Not at hcon
  set B : Fin k → Finset ι := fun i => {p ∈ Q | k * ∑ p' ∈ Q, f i p' < f i p * #Q}
  have hcover : Q ⊆ univ.biUnion B := fun p hp =>
    let ⟨i, hi⟩ := hcon p hp
    mem_biUnion.mpr ⟨i, mem_univ i, mem_filter.mpr ⟨hp, hi⟩⟩
  -- there is at least one function, which the strict inequality below needs
  obtain ⟨i₀, -⟩ := hcon _ hQ.choose_spec
  refine lt_irrefl (k * #Q) ?_
  calc k * #Q ≤ k * ∑ i, #(B i) :=
        Nat.mul_le_mul_left _ ((card_le_card hcover).trans card_biUnion_le)
    _ = ∑ i, k * #(B i) := mul_sum ..
    _ < ∑ _i : Fin k, #Q :=
        sum_lt_sum_of_nonempty ⟨i₀, mem_univ i₀⟩ fun i _ => mul_card_above_average_lt hQ k (f i)
    _ = k * #Q := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul]

end Finset
