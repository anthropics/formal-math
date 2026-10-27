/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Value.Defs

/-! # Sums inside the tables, products by groups, and the sum over θ_{a,b}

Proof of Lemma 1, end of the paragraph «The algorithm». This file proves two of the statements of
proof/networks/Value/Defs.lean:
* `stSumsInside`, «Together with the sums inside the tables»: a product over the groups of sums over
  the settings of the nodes of the group is one sum over the settings of all nodes;
* `stSumOut`, «Each θ_{a,b} occurs only in f_{a,b} and f_{b,a}, and Σ_{θ_{a,b}∈{0,1}^{c_{a,b}}}
  f_{a,b}(z_a, θ_{a,b}) f_{b,a}(z_b, θ_{a,b}) = Ψ_{a,b}(z_a, z_b)»;
and two facts on products, used for the joint sum: every pair of nodes inside a group lies in
exactly one group (`prod_inside`), and the ordered pairs (a, b) with a in the group γ and b outside
it, taken over all γ, are the unordered pairs of nodes in different groups, each in both orders
(`prod_across`). -/

public section

namespace Value

open Groundwork Groundwork.Prog Finset Eight.SecNetworks

/-- «Together with the sums inside the tables»: every node lies in exactly one group, so a family
(z_γ)_γ of settings of the groups is one choice z of a setting for every node. -/
theorem stSumsInside : StSumsInside := by
  intro g K χ S F
  rw [Finset.prod_univ_sum]
  symm
  refine Finset.sum_nbij' (fun z γ a => if χ a = γ then z a else []) (fun Z a => Z (χ a) a) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    rw [Fintype.mem_piFinset] at hz ⊢
    intro γ
    exact (mem_tuples _ _ _ _).2 fun a => ⟨fun h => by simp [h, hz a], fun h => by simp [h]⟩
  · intro Z hZ
    rw [Fintype.mem_piFinset] at hZ ⊢
    intro a
    exact ((mem_tuples _ _ _ _).1 (hZ (χ a)) a).1 rfl
  · intro z _
    funext a
    simp
  · intro Z hZ
    rw [Fintype.mem_piFinset] at hZ
    funext γ a
    by_cases h : χ a = γ
    · subst h
      simp
    · simp [h, ((mem_tuples _ _ _ _).1 (hZ γ) a).2 h]
  · intro z _
    rfl

variable {g K : ℕ}

/-- The pairs {a, b} inside the group γ, over all γ, are the pairs of nodes in the same group. -/
theorem prod_inside (χ : Fin g → Fin K) (F : Fin g × Fin g → ℤ) :
    ∏ γ, ∏ p ∈ pairs (Fin g) with χ p.1 = γ ∧ χ p.2 = γ, F p = ∏ p ∈ pairs (Fin g) with χ p.1 = χ p.2, F p := by
  rw [← Finset.prod_fiberwise ((pairs (Fin g)).filter fun p => χ p.1 = χ p.2) (fun p => χ p.1)]
  refine Finset.prod_congr rfl fun γ _ => ?_
  rw [Finset.filter_filter]
  refine Finset.prod_congr (Finset.filter_congr fun p _ => ⟨fun h => ⟨h.1.trans h.2.symm, h.1⟩, fun h => ⟨h.2, h.1 ▸ h.2⟩⟩) fun _ _ => rfl

/-- The ordered pairs (a, b) with a in the group γ and b outside it, over all γ, are the pairs {a,
b} of nodes in different groups, each in both orders. -/
theorem prod_across (χ : Fin g → Fin K) (F : Fin g × Fin g → ℤ) :
    ∏ γ, ∏ p : Fin g × Fin g with χ p.1 = γ ∧ χ p.2 ≠ γ, F p = ∏ p ∈ pairs (Fin g) with χ p.1 ≠ χ p.2, F p * F p.swap := by
  have h1 : ∏ γ, ∏ p : Fin g × Fin g with χ p.1 = γ ∧ χ p.2 ≠ γ, F p = ∏ p : Fin g × Fin g with χ p.1 ≠ χ p.2, F p := by
    rw [← Finset.prod_fiberwise (univ.filter fun p : Fin g × Fin g => χ p.1 ≠ χ p.2) (fun p => χ p.1)]
    refine Finset.prod_congr rfl fun γ _ => ?_
    rw [Finset.filter_filter]
    refine Finset.prod_congr (Finset.filter_congr fun p _ => ⟨fun h => ⟨fun e => h.2 (e ▸ h.1), h.1⟩, fun h => ⟨h.2, fun e => h.1 (h.2.trans e.symm)⟩⟩) fun _ _ => rfl
  have h2 : ∏ p ∈ pairs (Fin g) with χ p.1 ≠ χ p.2, F p.swap = ∏ p : Fin g × Fin g with p.2 < p.1 ∧ χ p.1 ≠ χ p.2, F p := by
    refine Finset.prod_nbij' Prod.swap Prod.swap ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
    · intro p hp
      simp only [pairs, mem_filter, mem_univ, true_and] at hp
      exact mem_filter.2 ⟨mem_univ _, hp.1, hp.2.symm⟩
    · intro p hp
      simp only [mem_filter, mem_univ, true_and] at hp
      exact mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, hp.1⟩, hp.2.symm⟩
  rw [h1, Finset.prod_mul_distrib, h2, pairs, Finset.filter_filter, ← Finset.prod_union]
  · congr 1
    ext p
    simp only [mem_filter, mem_univ, true_and, mem_union]
    constructor
    · intro h
      rcases lt_trichotomy p.1 p.2 with h' | h' | h'
      · exact Or.inl ⟨h', h⟩
      · exact absurd (congrArg χ h') h
      · exact Or.inr ⟨h', h⟩
    · rintro (h | h) <;> exact h.2
  · rw [Finset.disjoint_left]
    intro p hp hp'
    exact lt_asymm (mem_filter.1 hp).2.1 (mem_filter.1 hp').2.1

/-- «Each θ_{a,b} occurs only in f_{a,b} and f_{b,a}, and Σ_{θ_{a,b}∈{0,1}^{c_{a,b}}} f_{a,b}(z_a,
θ_{a,b}) f_{b,a}(z_b, θ_{a,b}) = Ψ_{a,b}(z_a, z_b)»: the sum over all θ of the product over the
pairs is the product over the pairs of the sums, each sum is Ψ_{a,b}(z_a, z_b), and the pairs in the
same group and the pairs in different groups are all pairs. -/
theorem stSumOut : StSumOut := by
  intro g K P B N hN χ z hz
  rw [Fintype.mem_piFinset] at hz
  have hs : (pairs (Fin g)).filter (fun p => χ p.1 ≠ χ p.2) = univ.filter (Across χ) := by
    rw [pairs, Finset.filter_filter]
  unfold jointTerm blockStrings
  rw [← Finset.mul_sum, hs, sum_tuples_prod (Across χ) (fun p => words (N.c p.1 p.2)) [] fun p θ => N.f p.1 p.2 (z p.1) θ * N.f p.2 p.1 (z p.2) θ, ← hs, mul_assoc]
  congr 1
  rw [← Finset.prod_filter_mul_prod_filter_not (pairs (Fin g)) fun p => χ p.1 = χ p.2]
  congr 1
  refine Finset.prod_congr rfl fun p hp => ?_
  have hlt : p.1 < p.2 := (mem_filter.1 (mem_filter.1 hp).1).2
  exact (hN.fact p.1 p.2 hlt.ne (z p.1) (hz p.1) (z p.2) (hz p.2)).symm

end Value
