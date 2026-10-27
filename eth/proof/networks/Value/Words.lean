/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Value.Defs

/-! # «Exactly one»: general facts behind the changes of variables

The sentences «the two copies on every edge agree … one string in {0,1}^λ per edge» (after
Definition 3) and «one string θ_{a,b} ∈ {0,1}^{c_{a,b}} per pair {a,b} of nodes in different groups»
(proof of Lemma 1) are changes of the variable of a sum. The statements `StOneStringPerEdge` and
`StBlocks` say them as «exactly one». This file has what both proofs share:
* `existsUnique_pi`: exactly one choice at every index gives exactly one family;
* `existsUnique_tuple`: exactly one tuple has given entries;
* `existsUnique_of_sum`: if a map i carries all sums over T back to sums over s, then every property
  that exactly one element of T has is had by i(a) for exactly one a in s (take the indicator of the
  property as the summand);
* `getD_chunks_map`: where the block of an index begins when a string is cut into blocks of given
  lengths;
* `star_swap`: the string on an edge is the same seen from either end. -/

public section

namespace Value

open Groundwork Finset

/-- If at every index exactly one x is right, then exactly one family is right at every index. -/
theorem existsUnique_pi {ι X : Type*} (R : ι → X → Prop) (h : ∀ i, ∃! x, R i x) : ∃! f : ι → X, ∀ i, R i (f i) :=
  ⟨fun i => (h i).exists.choose, fun i => (h i).exists.choose_spec, fun _ hf' => funext fun i => (h i).unique (hf' i) (h i).exists.choose_spec⟩

/-- Exactly one tuple has the entries t i at the indices i with P i. -/
theorem existsUnique_tuple {ι X : Type*} [Fintype ι] [DecidableEq ι] (P : ι → Prop) [DecidablePred P] (T : ι → Finset X) (d : X) (t : ι → X) (ht : ∀ i, P i → t i ∈ T i) :
    ∃! b : ι → X, b ∈ tuples P T d ∧ ∀ i, P i → b i = t i := by
  refine ⟨fun i => if P i then t i else d, ⟨(mem_tuples _ _ _ _).2 fun i => ⟨fun hi => ?_, fun hi => ?_⟩, fun i hi => ?_⟩, fun b hb => funext fun i => ?_⟩
  · simp only [if_pos hi]
    exact ht i hi
  · simp only [if_neg hi]
  · simp only [if_pos hi]
  · by_cases hi : P i
    · simp only [if_pos hi]
      exact hb.2 i hi
    · simp only [if_neg hi]
      exact ((mem_tuples _ _ _ _).1 hb.1 i).2 hi

/-- If Σ_{a ∈ s} F(i a) = Σ_{b ∈ T} F(b) for all F, and exactly one b ∈ T has the property Q, then
exactly one a ∈ s is such that i a has the property Q. (With F the indicator of Q both sums count.) -/
theorem existsUnique_of_sum {α β : Type*} (s : Finset α) (T : Finset β) (i : α → β) (hsum : ∀ F : β → ℤ, ∑ a ∈ s, F (i a) = ∑ b ∈ T, F b)
    (Q : β → Prop) (hQ : ∃! b, b ∈ T ∧ Q b) : ∃! a, a ∈ s ∧ Q (i a) := by
  classical
  have h := hsum fun b => if Q b then 1 else 0
  simp only [Finset.sum_boole] at h
  obtain ⟨b, hb, hb'⟩ := hQ
  have hT : T.filter Q = {b} := by
    ext b'
    rw [mem_filter, mem_singleton]
    exact ⟨fun h' => hb' b' h', fun h' => h' ▸ hb⟩
  rw [hT, card_singleton] at h
  obtain ⟨a, ha⟩ := Finset.card_eq_one.1 (by exact_mod_cast h : #(s.filter fun a => Q (i a)) = 1)
  have hm : ∀ a', a' ∈ s ∧ Q (i a') ↔ a' = a := fun a' => by
    have h' := @mem_filter _ (fun a => Q (i a)) _ s a'
    rw [ha, mem_singleton] at h'
    exact h'.symm
  exact ⟨a, (hm a).2 rfl, fun a' ha' => (hm a').1 ha'⟩

/-- A string w is cut into blocks of the lengths f j, j in the list e. The block of the index i
begins after the blocks of the indices before i, and has f i positions. -/
theorem getD_chunks_map {ι : Type*} [BEq ι] [LawfulBEq ι] (f : ι → ℕ) (e : List ι) (w d : List Bool) {i : ι} (hi : i ∈ e) :
    (chunks (e.map f) w).getD (e.idxOf i) d = (w.drop ((e.map f).take (e.idxOf i)).sum).take (f i) := by
  induction e generalizing w with
  | nil => simp at hi
  | cons j e ih =>
    by_cases h : j = i
    · subst h
      simp [chunks]
    · have h' : (j == i) = false := by simpa using h
      have hi' : i ∈ e := (List.mem_cons.1 hi).resolve_left (Ne.symm h)
      simp only [List.getD_eq_getElem?_getD] at ih
      simp [chunks, List.idxOf_cons, h', ih _ hi']

/-- The string of Λ on the edge {w, w'} is the same seen from w and from w'. -/
theorem star_swap {K : ℕ} (Λ : Fin K × Fin K → List Bool) (w w' : Fin K) : star Λ w w' = star Λ w' w := by
  change Λ (min _ _, max _ _) = Λ (min _ _, max _ _)
  rw [min_comm, max_comm]

end Value
