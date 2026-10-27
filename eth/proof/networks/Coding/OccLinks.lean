/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Coding.OccLists
import all StepMachines.Prog.CountNet
import Mathlib.Tactic.Ring

/-! # The tests between two clusters and Lean's links

Section 6: «For a ≠ b, c_{a,b} is the number of tests with one occurrence in cluster a and the other
in cluster b. Choose an order of these tests, and let z_a|_b ∈ {0,1}^{c_{a,b}} list the bits of z_a
at their occurrences in cluster a».
`links_eq_tests`: for clusters a ≤ b the list `Coding.testsBetween g Φ a b`, with each occurrence
replaced by its place, is the list `Groundwork.Prog.Count.links g 3 Φ a b`, with each place of a
cluster replaced by its place in Φ. Both lists are increasing in the order of the dictionary, so it
is enough that they have the same members, and this is `mem_tests_iff` together with: the cluster of
an occurrence is the block of 3·m̄ places in which its place lies.
`import all StepMachines.Prog.CountNet` gives access to `locals_eq` and `mem_links`, which are not
public. -/

public section

namespace Coding

open Groundwork Groundwork.Prog Groundwork.Prog.Count

variable {g : ℕ} {Φ : Fml}

/-- If Φ has an occurrence, then m̄ ≥ 1. -/
theorem mu_pos_of_occ (hg : 0 < g) {o : ℕ × ℕ} (ho : o ∈ occAll Φ) : 0 < mu g Φ := by
  have h1 := fst_lt_of_mem_occAll ho
  have h2 := le_mul_mu hg Φ
  rcases Nat.eq_zero_or_pos (mu g Φ) with h | h
  · rw [h, Nat.mul_zero] at h2
    omega
  · exact h

/-- The cluster of an occurrence is the block of 3·m̄ places in which its place lies. -/
theorem clusterOf_eq_iff (hg : 0 < g) (h3 : ∀ C ∈ Φ, C.length ≤ 3) {o : ℕ × ℕ} (ho : o ∈ occAll Φ) (a : ℕ) :
    clusterOf g Φ o = a ↔ a * (mu g Φ * 3) ≤ place o ∧ place o < a * (mu g Φ * 3) + mu g Φ * 3 := by
  have h1 := mem_occAll.1 ho
  have h2 := length_getD_le h3 o.1
  have e : a * (mu g Φ * 3) = a * mu g Φ * 3 := by ring
  rw [clusterOf, div_eq_iff_block (mu_pos_of_occ hg ho), e]
  simp only [place]
  constructor <;> rintro ⟨_, _⟩ <;> constructor <;> omega

/-- The occurrences in cluster a are the occurrences whose cluster is a. -/
theorem mem_occOf_iff (hg : 0 < g) {o : ℕ × ℕ} {a : ℕ} : o ∈ occOf g Φ a ↔ o ∈ occAll Φ ∧ clusterOf g Φ o = a := by
  rw [occOf, mem_occIn, mem_occAll, clusterOf]
  constructor
  · rintro ⟨h1, h2, h4⟩
    exact ⟨h4, (div_eq_iff_block (by omega)).2 ⟨h1, h2⟩⟩
  · rintro ⟨h4, hc⟩
    obtain ⟨h1, h2⟩ := (div_eq_iff_block (mu_pos_of_occ hg (mem_occAll.2 h4))).1 hc
    exact ⟨h1, h2, h4⟩

/-- The tests between the clusters a and b do not depend on the order in which the clusters are
named. -/
theorem testsBetween_comm (a b : ℕ) : testsBetween g Φ a b = testsBetween g Φ b a := List.filter_congr fun _ _ => Bool.or_comm _ _

/-- For a ≤ b the earlier occurrence of a test between the clusters a and b lies in cluster a. -/
theorem mem_testsBetween (h3 : ∀ C ∈ Φ, C.length ≤ 3) {a b : ℕ} (hab : a ≤ b) {p : (ℕ × ℕ) × (ℕ × ℕ)} :
    p ∈ testsBetween g Φ a b ↔ p ∈ tests Φ ∧ clusterOf g Φ p.1 = a ∧ clusterOf g Φ p.2 = b := by
  simp only [testsBetween, List.mem_filter, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  refine and_congr_right fun hp => ⟨?_, Or.inl⟩
  rintro (h | ⟨h1, h2⟩)
  · exact h
  · obtain ⟨o, o'⟩ := p
    obtain ⟨ho, ho', hl⟩ := (mem_tests_iff h3).1 hp
    have hlt := ((linkB_iff_places _ _).1 hl).1
    have hle : clusterOf g Φ o ≤ clusterOf g Φ o' := by
      have k1 := mem_occAll.1 ho
      have k2 := length_getD_le h3 o.1
      have k3 := mem_occAll.1 ho'
      have k4 := length_getD_le h3 o'.1
      simp only [place] at hlt
      exact Nat.div_le_div_right (by omega)
    have h1' : clusterOf g Φ o = b := h1
    have h2' : clusterOf g Φ o' = a := h2
    change clusterOf g Φ o = a ∧ clusterOf g Φ o' = b
    constructor <;> omega

/-- The tests, read as pairs of places, are listed in the order of the dictionary. -/
theorem pairwise_tests (h3 : ∀ C ∈ Φ, C.length ≤ 3) : ((tests Φ).map fun p => (place p.1, place p.2)).Pairwise lexLt := by
  rw [List.pairwise_map]
  refine ((pairwise_product (pairwise_occIn h3 0 Φ.length) (pairwise_occIn h3 0 Φ.length)).filter _).imp ?_
  rintro p q (h | ⟨h1, h2⟩)
  · exact Or.inl h
  · exact Or.inr ⟨congrArg place h1, h2⟩

/-- The tests between two clusters are Lean's links, in the same order («Choose an order of these
tests», Section 6). -/
theorem links_eq_tests (hg : 0 < g) (h3 : ∀ C ∈ Φ, C.length ≤ 3) {a b : ℕ} (hab : a ≤ b) :
    (links g 3 Φ a b).map (fun p => (a * (mu g Φ * 3) + p.1, b * (mu g Φ * 3) + p.2)) = (testsBetween g Φ a b).map fun p => (place p.1, place p.2) := by
  refine eq_of_lex ?_ ?_ fun q => ⟨fun hq => ?_, fun hq => ?_⟩
  · rw [List.pairwise_map, links, locals_eq hg]
    refine ((pairwise_product List.pairwise_lt_range List.pairwise_lt_range).filter _).imp ?_
    rintro p q (h | ⟨h1, h2⟩)
    · exact Or.inl (Nat.add_lt_add_left h _)
    · exact Or.inr ⟨congrArg (a * (mu g Φ * 3) + ·) h1, Nat.add_lt_add_left h2 _⟩
  · exact (pairwise_tests h3).sublist (List.filter_sublist.map _)
  · obtain ⟨⟨r, r'⟩, hp, rfl⟩ := List.mem_map.1 hq
    have hp' := (mem_links hg a b (r, r')).1 hp
    have hr : r < mu g Φ * 3 := hp'.1
    have hr' : r' < mu g Φ * 3 := hp'.2.1
    have hl : linkB 3 Φ (a * (mu g Φ * 3) + r) (b * (mu g Φ * 3) + r') = true := hp'.2.2
    obtain ⟨-, hs, hv, -⟩ := (linkB_iff_places _ _).1 hl
    obtain ⟨v, hv1⟩ := Option.isSome_iff_exists.1 hs
    have ho := mem_occAll_of_varAt hv1
    have ho' := mem_occAll_of_varAt (hv.symm.trans hv1)
    refine List.mem_map.2 ⟨(((a * (mu g Φ * 3) + r) / 3, (a * (mu g Φ * 3) + r) % 3), ((b * (mu g Φ * 3) + r') / 3, (b * (mu g Φ * 3) + r') % 3)), (mem_testsBetween h3 hab).2 ⟨?_, ?_, ?_⟩, ?_⟩
    · exact (mem_tests_iff h3).2 ⟨ho, ho', by rw [place_div_mod, place_div_mod]; exact hl⟩
    · refine (clusterOf_eq_iff hg h3 ho a).2 ?_
      rw [place_div_mod]
      omega
    · refine (clusterOf_eq_iff hg h3 ho' b).2 ?_
      rw [place_div_mod]
      omega
    · simp only [place_div_mod]
  · obtain ⟨⟨o, o'⟩, hp, rfl⟩ := List.mem_map.1 hq
    obtain ⟨ht, h1, h2⟩ := (mem_testsBetween h3 hab).1 hp
    obtain ⟨ho, ho', hl⟩ := (mem_tests_iff h3).1 ht
    obtain ⟨c1, c2⟩ := (clusterOf_eq_iff hg h3 ho a).1 h1
    obtain ⟨c3, c4⟩ := (clusterOf_eq_iff hg h3 ho' b).1 h2
    refine List.mem_map.2 ⟨(place o - a * (mu g Φ * 3), place o' - b * (mu g Φ * 3)), (mem_links hg a b _).2 ⟨?_, ?_, ?_⟩, ?_⟩
    · change place o - a * (mu g Φ * 3) < mu g Φ * 3
      omega
    · change place o' - b * (mu g Φ * 3) < mu g Φ * 3
      omega
    · change linkB 3 Φ (a * (mu g Φ * 3) + (place o - a * (mu g Φ * 3))) (b * (mu g Φ * 3) + (place o' - b * (mu g Φ * 3))) = true
      rw [Nat.add_sub_cancel' c1, Nat.add_sub_cancel' c3]
      exact hl
    · change (a * (mu g Φ * 3) + (place o - a * (mu g Φ * 3)), b * (mu g Φ * 3) + (place o' - b * (mu g Φ * 3))) = (place o, place o')
      rw [Nat.add_sub_cancel' c1, Nat.add_sub_cancel' c3]

/-- Whatever is read off the links of Lean's network, place by place, is read off the tests. -/
theorem map_links (hg : 0 < g) (h3 : ∀ C ∈ Φ, C.length ≤ 3) {a b : ℕ} (hab : a ≤ b) {β : Type} (F : ℕ × ℕ → β) :
    (links g 3 Φ a b).map (fun p => F (a * (mu g Φ * 3) + p.1, b * (mu g Φ * 3) + p.2)) = (testsBetween g Φ a b).map fun p => F (place p.1, place p.2) := by
  have h := congrArg (List.map F) (links_eq_tests hg h3 hab)
  rw [List.map_map, List.map_map] at h
  exact h

/-- «c_{a,b} is the number of tests with one occurrence in cluster a and the other in cluster b»
(Section 6): Lean's number c_{a,b} is the number of tests between the clusters a and b. -/
theorem capF_eq (hg : 0 < g) (h3 : ∀ C ∈ Φ, C.length ≤ 3) (a b : ℕ) : capF g 3 Φ a b = (testsBetween g Φ a b).length := by
  have key : ∀ {a b : ℕ}, a ≤ b → (links g 3 Φ a b).length = (testsBetween g Φ a b).length := by
    intro a b hab
    have h := congrArg List.length (links_eq_tests hg h3 hab)
    rwa [List.length_map, List.length_map] at h
  unfold capF
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h, key h]
  · rw [min_eq_right h, max_eq_left h, key h, testsBetween_comm]

end Coding
