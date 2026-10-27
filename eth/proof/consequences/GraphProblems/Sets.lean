/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GraphProblems.Interfaces
public import GraphProblems.Read

/-! # Corollary 7: what the formulas of Independent Set and Dominating Set say

An assignment a to x₀ … xₙ₋₁ is the set S = {v | a v = true} of vertices. This file shows that a
satisfies the formula of Independent Set if and only if S is an independent set, and the formula of
Dominating Set if and only if S is a
dominating set, so that the number of satisfying assignments with exactly s true variables is the
number of such sets of size s. It also bounds the width, the variables and the number of clauses of
a formula with one clause of two literals for each chosen pair of vertices,
and derives the decision problems from the numbers of independent sets, cliques, vertex covers and
dominating sets of a given size. -/

public section

namespace GraphProblems

open Groundwork Groundwork.Prog CountKSat Finset

namespace Sets

variable {n : ℕ}

/-- The set of the variables that an assignment makes true. -/
def trueSet (a : Fin n → Bool) : Finset (Fin n) := univ.filter fun i => a i = true

/-- A variable is in the set if and only if it is true. -/
theorem mem_trueSet {a : Fin n → Bool} {i : Fin n} : i ∈ trueSet a ↔ a i = true := by simp [trueSet]

/-- If the assignments that satisfy ψ are those whose set has the property P, then ψ has as many
satisfying assignments with s true variables as there are sets of size s with the property P. -/
theorem cntS_eq_ncard (s : ℕ) (ψ : Fml) (P : Finset (Fin n) → Prop)
    (h : ∀ a : Fin n → Bool, (∀ C ∈ ψ, ∃ l ∈ C, CountKSat.ext a l.1 = l.2) ↔ P (trueSet a)) :
    cntS n s ψ = {S : Finset (Fin n) | P S ∧ S.card = s}.ncard := by
  classical
  have h1 : {S : Finset (Fin n) | P S ∧ S.card = s} = ↑(univ.filter fun S : Finset (Fin n) => P S ∧ S.card = s) := by
    ext S; simp
  rw [h1, Set.ncard_coe_finset, cntS]
  refine card_nbij' trueSet (fun S i => decide (i ∈ S)) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ha ⊢
    exact ⟨(h a).1 ha.1, ha.2⟩
  · intro S hS
    have hS' : trueSet (fun i => decide (i ∈ S)) = S := by ext i; simp [trueSet]
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hS ⊢
    refine ⟨(h _).2 (by rw [hS']; exact hS.1), ?_⟩
    have := hS.2
    rw [← hS'] at this
    exact this
  · intro a _
    funext i
    simp [trueSet]
  · intro S _
    ext i; simp [trueSet]

/-- The pairs are those of two numbers below n. -/
theorem mem_pairs {n : ℕ} {p : ℕ × ℕ} : p ∈ pairs n ↔ p.1 < n ∧ p.2 < n := by
  obtain ⟨u, v⟩ := p
  simp [pairs]

/-- An assignment satisfies the formula with one clause of two literals of the same sign b for every
pair chosen by q if and only if, for every such pair, one of its two variables has the value b. -/
theorem sat_pairs_iff (q : ℕ × ℕ → Bool) (b : Bool) (a : Fin n → Bool) :
    (∀ C ∈ ((pairs n).filter q).map fun p => [(p.1, b), (p.2, b)], ∃ l ∈ C, CountKSat.ext a l.1 = l.2)
      ↔ ∀ u v : Fin n, q (u.val, v.val) = true → a u = b ∨ a v = b := by
  simp only [List.forall_mem_map, List.mem_filter, mem_pairs, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
  constructor
  · intro H u v hq
    simpa [CountKSat.ext, u.2, v.2] using H (u.val, v.val) ⟨⟨u.2, v.2⟩, hq⟩
  · rintro H ⟨u, v⟩ ⟨⟨hu, hv⟩, hq⟩
    simpa [CountKSat.ext, hu, hv] using H ⟨u, hu⟩ ⟨v, hv⟩ hq

/-- Width, variables and number of clauses of such a formula. -/
theorem shaped_pairs (n : ℕ) (q : ℕ × ℕ → Bool) (b : Bool) :
    Shaped 2 n (((pairs n).filter q).map fun p => [(p.1, b), (p.2, b)]) ∧ (((pairs n).filter q).map fun p => [(p.1, b), (p.2, b)]).length ≤ n * n := by
  constructor
  · intro C hC
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hC
    have hp' := mem_pairs.1 (List.mem_filter.1 hp).1
    refine ⟨by simp, fun l hl => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact hp'.1
    · exact hp'.2
  · rw [List.length_map]
    refine (List.length_filter_le _ _).trans ?_
    simp [pairs, List.length_product]

variable (G : SimpleGraph (Fin n)) (a : Fin n → Bool)

/-- An assignment satisfies the formula of Independent Set if and only if its set is independent. -/
theorem sat_indepF : (∀ C ∈ indepF n (matrix G), ∃ l ∈ C, CountKSat.ext a l.1 = l.2) ↔ G.IsIndepSet (trueSet a : Set (Fin n)) := by
  rw [indepF, sat_pairs_iff]
  constructor
  · intro H u hu v hv _ huv
    have := H u v ((stAdj n G u v).2 huv)
    rw [mem_coe, mem_trueSet] at hu hv
    simp [hu, hv] at this
  · intro H u v huv
    have huv' := (stAdj n G u v).1 huv
    by_contra hc
    simp only [not_or, Bool.not_eq_false] at hc
    exact H (mem_coe.2 (mem_trueSet.2 hc.1)) (mem_coe.2 (mem_trueSet.2 hc.2)) huv'.ne huv'

/-- An assignment satisfies the formula of Dominating Set if and only if its set is dominating. -/
theorem sat_domF : (∀ C ∈ domF n (matrix G), ∃ l ∈ C, CountKSat.ext a l.1 = l.2) ↔ IsDominating G (trueSet a) := by
  constructor
  · intro H v
    obtain ⟨l, hl, hal⟩ := H (posC (v.val :: (List.range n).filter fun u => u != v.val && adjB n (matrix G) v.val u))
      (List.mem_map.2 ⟨_, List.mem_map.2 ⟨v.val, List.mem_range.2 v.2, rfl⟩, rfl⟩)
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hl
    rcases List.mem_cons.1 hu with rfl | hu
    · left
      simpa [CountKSat.ext, v.2, mem_trueSet] using hal
    · right
      obtain ⟨hun, huv⟩ := List.mem_filter.1 hu
      rw [List.mem_range] at hun
      simp only [Bool.and_eq_true, bne_iff_ne] at huv
      refine ⟨⟨u, hun⟩, ?_, (stAdj n G v ⟨u, hun⟩).1 huv.2⟩
      simpa [CountKSat.ext, hun, mem_trueSet] using hal
  · intro H C hC
    obtain ⟨D, hD, rfl⟩ := List.mem_map.1 hC
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hD
    rw [List.mem_range] at hv
    rcases H ⟨v, hv⟩ with h | ⟨u, hu, huv⟩
    · refine ⟨(v, true), List.mem_map.2 ⟨v, by simp, rfl⟩, ?_⟩
      simpa [CountKSat.ext, hv, mem_trueSet] using h
    · refine ⟨(u.val, true), List.mem_map.2 ⟨u.val, List.mem_cons_of_mem _ (List.mem_filter.2 ⟨List.mem_range.2 u.2, ?_⟩), rfl⟩, ?_⟩
      · simp only [Bool.and_eq_true, bne_iff_ne]
        exact ⟨fun e => huv.ne (Fin.ext e.symm), (stAdj n G ⟨v, hv⟩ u).2 huv⟩
      · simpa [CountKSat.ext, u.2, mem_trueSet] using hu

end Sets

open Sets

/-- The formula of Independent Set has as many satisfying assignments with s true variables as the
graph has independent sets of size s. -/
theorem stIndep : StIndep := fun n G s => by
  rw [cntS_eq_ncard s _ (fun S => G.IsIndepSet (S : Set (Fin n))) (sat_indepF G), numIndepSets]
  congr 1
  ext S
  exact (G.isNIndepSet_iff s S).symm

/-- `StDom`: for the formula `domF` of a graph G, `cntS n s` is the number of dominating sets of G
with s vertices. -/
theorem stDom : StDom := fun _ G s => cntS_eq_ncard s _ (fun S => IsDominating G S) (sat_domF G)

/-- There is an independent set or a clique with at least s vertices, or a vertex cover or a
dominating set with at most s ≤ n vertices, if and only if the number of those of size exactly s is
not 0. -/
theorem stDecide : StDecide := fun n G s hs => by
  have hne : ∀ P : Finset (Fin n) → Prop, {S : Finset (Fin n) | P S}.ncard ≠ 0 ↔ ∃ S, P S := fun P => by
    rw [← pos_iff_ne_zero, Set.ncard_pos]
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [numIndepSets, hne]
    constructor
    · rintro ⟨S, hS, hc⟩
      obtain ⟨T, hT, hTc⟩ := exists_subset_card_eq hc
      exact ⟨T, ⟨Set.Pairwise.mono (coe_subset.2 hT) hS, hTc⟩⟩
    · rintro ⟨S, hS⟩
      exact ⟨S, hS.1, hS.2.ge⟩
  · rw [numCliques, hne]
    constructor
    · rintro ⟨S, hS, hc⟩
      obtain ⟨T, hT, hTc⟩ := exists_subset_card_eq hc
      exact ⟨T, ⟨hS.subset (coe_subset.2 hT), hTc⟩⟩
    · rintro ⟨S, hS⟩
      exact ⟨S, hS.1, hS.2.ge⟩
  · rw [numVertexCovers, hne]
    constructor
    · rintro ⟨S, hS, hc⟩
      obtain ⟨T, hT, -, hTc⟩ := exists_subsuperset_card_eq (subset_univ S) hc (by simpa using hs)
      exact ⟨T, hS.subset (coe_subset.2 hT), hTc⟩
    · rintro ⟨S, hS, hc⟩
      exact ⟨S, hS, hc.le⟩
  · rw [numDominatingSets, hne]
    constructor
    · rintro ⟨S, hS, hc⟩
      obtain ⟨T, hT, -, hTc⟩ := exists_subsuperset_card_eq (subset_univ S) hc (by simpa using hs)
      refine ⟨T, fun v => ?_, hTc⟩
      rcases hS v with h | ⟨u, hu, huv⟩
      · exact Or.inl (hT h)
      · exact Or.inr ⟨u, hT hu, huv⟩
    · rintro ⟨S, hS, hc⟩
      exact ⟨S, hS, hc.le⟩

end GraphProblems
