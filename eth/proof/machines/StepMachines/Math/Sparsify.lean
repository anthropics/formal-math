/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Order.Ring.Nat

/-! Lemmas for the sparsification of a 3-CNF (Impagliazzo, Paturi, Zane): formulas as finite sets of
clauses,
their reduction to inclusion-minimal clauses, what holds at a node of the branching tree, and a
double counting of clauses.
Literals are elements of any type α; a clause is a Finset α, a formula a Finset (Finset α). -/

namespace Groundwork.Sparsify

open Finset

variable {α : Type*} [DecidableEq α]

/-- The truth values v of the literals satisfy F: every clause has a true literal. -/
@[expose] public def Sat (v : α → Prop) (F : Finset (Finset α)) : Prop := ∀ C ∈ F, ∃ l ∈ C, v l

/-- No clause properly contains another. -/
@[expose] public def Reduced (F : Finset (Finset α)) : Prop := ∀ C ∈ F, ∀ D ∈ F, D ⊆ C → D = C

/-- The inclusion-minimal clauses. -/
@[expose] public def red (F : Finset (Finset α)) : Finset (Finset α) := F.filter fun C => ∀ D ∈ F, D ⊆ C → D = C

/-- The i-clauses of F that contain S. -/
@[expose] public def over (F : Finset (Finset α)) (i : ℕ) (S : Finset α) : Finset (Finset α) :=
  F.filter fun C => C.card = i ∧ S ⊆ C

/-- The 1-clauses of F. -/
@[expose] public def ones (F : Finset (Finset α)) : Finset (Finset α) := F.filter fun C => C.card = 1

public theorem red_subset (F : Finset (Finset α)) : red F ⊆ F := filter_subset _ _

public theorem reduced_red (F : Finset (Finset α)) : Reduced (red F) := by
  intro C hC D hD h
  exact (mem_filter.1 hC).2 D (red_subset F hD) h

public theorem exists_red_subset {F : Finset (Finset α)} {C : Finset α} (hC : C ∈ F) : ∃ D ∈ red F, D ⊆ C := by
  induction hn : C.card using Nat.strong_induction_on generalizing C with
  | _ n ih =>
    by_cases h : ∀ D ∈ F, D ⊆ C → D = C
    · exact ⟨C, mem_filter.2 ⟨hC, h⟩, Subset.refl _⟩
    · simp only [not_forall] at h
      obtain ⟨D, hD, hDC, hne⟩ := h
      have hlt : D.card < n := hn ▸ card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hDC, hne⟩)
      obtain ⟨E, hE, hED⟩ := ih _ hlt hD rfl
      exact ⟨E, hE, hED.trans hDC⟩

/-- sat(red F) = sat(F). -/
public theorem sat_red (v : α → Prop) (F : Finset (Finset α)) : Sat v (red F) ↔ Sat v F := by
  constructor
  · intro h C hC
    obtain ⟨D, hD, hDC⟩ := exists_red_subset hC
    obtain ⟨l, hl, hv⟩ := h D hD
    exact ⟨l, hDC hl, hv⟩
  · intro h C hC
    exact h C (red_subset F hC)

section Add

variable {τ : ℕ} {F A : Finset (Finset α)}

end Add

/-- The invariant at a node of the tree: F is reduced, and N is a set of 2-clauses of F
with at most τ clauses at each literal. -/
structure Inv (τ : ℕ) (F N : Finset (Finset α)) : Prop where
  red : Reduced F
  sub : N ⊆ F
  two : ∀ C ∈ N, C.card = 2
  deg : ∀ a, (N.filter fun C => a ∈ C).card ≤ τ

section Step

variable {τ : ℕ} {F A N : Finset (Finset α)}

end Step

section Branch

variable {τ : ℕ} {F P : Finset (Finset α)} {H : Finset α}

end Branch

/-- What holds of a node F of the tree of φ, with counters p and q: every clause of F is a subset
of a clause of φ, and for some N with `Inv` the potentials |N| + (τ+1)·|ones F| and |N| + 2τ·|ones
F| are at least
p and q. -/
public def Node (τ : ℕ) (φ F : Finset (Finset α)) (p q : ℕ) : Prop :=
  (∀ C ∈ F, ∃ C' ∈ φ, C ⊆ C' ∧ (C'.Nonempty → C.Nonempty)) ∧
    ∃ N, Inv τ F N ∧ p ≤ N.card + (τ + 1) * (ones F).card ∧ q ≤ N.card + 2 * τ * (ones F).card

section Node

variable {τ : ℕ} {φ F P : Finset (Finset α)} {H : Finset α} {p q : ℕ}

public theorem node_root (τ : ℕ) (φ : Finset (Finset α)) : Node τ φ (red φ) 0 0 :=
  ⟨fun C hC => ⟨C, red_subset φ hC, Subset.refl _, id⟩,
    ∅, ⟨reduced_red φ, empty_subset _, by simp, by simp⟩, Nat.zero_le _, Nat.zero_le _⟩

end Node

section Count

variable {τ n : ℕ} {φ F : Finset (Finset α)} {p q : ℕ} {U : Finset α}

/-- Double counting: i-subsets of U, each point in at most d of them. -/
theorem mul_card_le (U : Finset α) (G : Finset (Finset α)) (i d : ℕ) (hU : ∀ C ∈ G, C ⊆ U)
    (hi : ∀ C ∈ G, C.card = i) (hd : ∀ a, (G.filter fun C => a ∈ C).card ≤ d) : i * G.card ≤ U.card * d := by
  have := sum_card_inter_le (s := U) (B := G) (n := d) fun a _ => hd a
  rw [sum_congr rfl fun C hC => by rw [inter_eq_right.2 (hU C hC), hi C hC], sum_const] at this
  simpa [Nat.mul_comm] using this

theorem card_ones_le (hU : ∀ C ∈ F, C ⊆ U) : (ones F).card ≤ U.card := by
  have := mul_card_le U (ones F) 1 1 (fun C hC => hU C (mem_filter.1 hC).1) (fun C hC => (mem_filter.1 hC).2)
    (fun a => ?_)
  · omega
  · rw [card_le_one]
    intro C hC D hD
    obtain ⟨hC, haC⟩ := mem_filter.1 hC
    obtain ⟨hD, haD⟩ := mem_filter.1 hD
    obtain ⟨c, rfl⟩ := card_eq_one.1 (mem_filter.1 hC).2
    obtain ⟨d, rfl⟩ := card_eq_one.1 (mem_filter.1 hD).2
    rw [mem_singleton] at haC haD
    rw [← haC, ← haD]

end Count

end Groundwork.Sparsify
