/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Net.Defs
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Finset.Card

/-! # Step 3 of Appendix D: first facts on the list of objects

What the files of proof/variables/VariableBound/Net share and what has no counterpart in the network
with one kind of marks of `PaddedDescent.F`: which triples (κ, e, j) are objects, that no object
occurs twice, that every object has a clause of ψ, how many objects
there are of each kind. -/

public section

namespace VariableBound.Net.Basic

open Groundwork Groundwork.Prog PaddedDescent.F
open PaddedDescent.F.Mark (Cl qv vio WfL occ)

variable {k g n : ℕ} {D : Dat}

/-- The objects are the triples (0, e, 0) with e < m and the triples (1, e, j) with j < r and e ∈
Λ_j. -/
theorem mem_objs {x : ℕ × ℕ × ℕ} : x ∈ objs D ↔
    (x.1 = 0 ∧ x.2.1 < D.1.length ∧ x.2.2 = 0) ∨ (x.1 = 1 ∧ x.2.2 < D.2.length ∧ x.2.1 ∈ D.2.getD x.2.2 []) := by
  obtain ⟨κ, e, j⟩ := x
  simp only [objs, List.mem_append, List.mem_map, List.mem_range, List.mem_flatMap, Prod.mk.injEq]
  constructor
  · rintro (⟨e', h, h0, h1, h2⟩ | ⟨j', hj, e', he, h0, h1, h2⟩)
    · subst h0 h1 h2; exact Or.inl ⟨rfl, h, rfl⟩
    · subst h0 h1 h2; exact Or.inr ⟨rfl, hj, he⟩
  · rintro (⟨h0, h, h2⟩ | ⟨h0, hj, he⟩)
    · exact Or.inl ⟨e, h, h0.symm, rfl, h2.symm⟩
    · exact Or.inr ⟨j, hj, e, he, h0.symm, rfl, rfl⟩

/-- At a place o below the number of objects, `obAt` is the entry of the list. -/
theorem obAt_eq {o : ℕ} (h : o < (objs D).length) : obAt D o = (objs D)[o] := by
  rw [obAt, List.getD_eq_getElem _ _ h]

/-- At a place o below the number of objects, `obAt` is an object. -/
theorem obAt_mem {o : ℕ} (h : o < (objs D).length) : obAt D o ∈ objs D := by
  rw [obAt_eq h]; exact List.getElem_mem h

/-- Every object stands at some place of the list. -/
theorem exists_obAt {x : ℕ × ℕ × ℕ} (h : x ∈ objs D) : ∃ o < (objs D).length, obAt D o = x := by
  obtain ⟨o, ho, rfl⟩ := List.getElem_of_mem h
  exact ⟨o, ho, obAt_eq ho⟩

/-- There are two kinds. -/
theorem kind_lt {o : ℕ} (h : o < (objs D).length) : (obAt D o).1 < 2 := by
  rcases mem_objs.1 (obAt_mem h) with h | h <;> omega

/-- An object (at a place o below the number of objects) is of kind 0 or of kind 1. -/
theorem kind_cases {o : ℕ} (h : o < (objs D).length) : (obAt D o).1 = 0 ∨ (obAt D o).1 = 1 := by
  have := kind_lt h; omega

/-- An incidence (E, j) has j < r and E ∈ Λ_j. -/
theorem inc_mem {o : ℕ} (h : o < (objs D).length) (h1 : (obAt D o).1 = 1) :
    (obAt D o).2.2 < D.2.length ∧ (obAt D o).2.1 ∈ D.2.getD (obAt D o).2.2 [] := by
  rcases mem_objs.1 (obAt_mem h) with h' | h'
  · omega
  · exact h'.2

/-- Check number j < r is a member of the list of checks. -/
theorem getD_mem {j : ℕ} (h : j < D.2.length) : D.2.getD j [] ∈ D.2 := by
  rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h

/-- For well-formed data (WfD), the clause of an object is a clause of ψ: its number is below m. -/
theorem cl_lt (hW : WfD k n D) {o : ℕ} (h : o < (objs D).length) : (obAt D o).2.1 < D.1.length := by
  rcases mem_objs.1 (obAt_mem h) with h' | h'
  · exact h'.2.1
  · exact (hW.2 _ (getD_mem h'.2.1)).2 _ h'.2.2

/-- For well-formed data (WfD), the clause of an object is a member of ψ. -/
theorem clOf_mem (hW : WfD k n D) {o : ℕ} (h : o < (objs D).length) : clOf D o ∈ D.1 := by
  rw [clOf, List.getD_eq_getElem _ _ (cl_lt hW h)]; exact List.getElem_mem _

/-- For well-formed data (WfD), the clause of an object has 1 to k literals on variables below n. -/
theorem clOf_wf (hW : WfD k n D) {o : ℕ} (h : o < (objs D).length) :
    clOf D o ≠ [] ∧ (clOf D o).length ≤ k ∧ ∀ l ∈ clOf D o, l.1 < n :=
  hW.1 D.1 (by simp) _ (clOf_mem hW h)

/-- For well-formed data (WfD), no object occurs twice in the list. -/
theorem nodup_objs (hW : WfD k n D) : (objs D).Nodup := by
  unfold objs
  refine List.Nodup.append ?_ ?_ ?_
  · exact List.Nodup.map (fun a b h => by simpa using h) List.nodup_range
  · rw [List.nodup_flatMap]
    refine ⟨fun j hj => ?_, ?_⟩
    · exact List.Nodup.map (fun a b h => by simpa using h) (hW.2 _ (getD_mem (List.mem_range.1 hj))).1
    · refine List.Pairwise.imp_of_mem ?_ (List.nodup_range (n := D.2.length))
      intro j j' _ _ hne
      simp only [Function.onFun, List.disjoint_left, List.mem_map, not_exists, not_and]
      rintro x ⟨e, _, rfl⟩ e' _ h
      simp only [Prod.mk.injEq, true_and] at h
      exact hne h.2.symm
  · simp only [List.disjoint_left, List.mem_map, List.mem_flatMap, not_exists, not_and]
    rintro x ⟨e, _, rfl⟩ j _ e' _ h
    simp at h

/-- For well-formed data (WfD), two places below the number of objects that hold the same triple are
equal. -/
theorem obAt_inj (hW : WfD k n D) {o o' : ℕ} (h : o < (objs D).length) (h' : o' < (objs D).length) (he : obAt D o = obAt D o') : o = o' := by
  rw [obAt_eq h, obAt_eq h'] at he
  exact (List.Nodup.getElem_inj_iff (nodup_objs hW)).1 he

/-- I + m: the number of objects. -/
theorem length_objs : (objs D).length = D.1.length + (D.2.map List.length).sum := by
  have h : ∀ L : List (List ℕ), (((List.range L.length).map fun j => (L.getD j []).length)) = L.map List.length := by
    intro L
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.length_map, List.length_range] at h1
    rw [List.getElem_map, List.getElem_map, List.getElem_range, List.getD_eq_getElem _ _ h1]
  simp only [objs, List.length_append, List.length_map, List.length_range, List.length_flatMap]
  rw [h]

/-- The first m objects are the clauses. -/
theorem obAt_of_lt {o : ℕ} (h : o < D.1.length) : obAt D o = (0, o, 0) := by
  have h1 : o < ((List.range D.1.length).map fun e => ((0 : ℕ), e, (0 : ℕ))).length := by simpa using h
  rw [obAt, objs, List.getD_append _ _ _ _ h1, List.getD_eq_getElem _ _ h1, List.getElem_map, List.getElem_range]

/-- For well-formed data (WfD), an object is a clause iff it is among the first m. -/
theorem kind_zero_iff (hW : WfD k n D) {o : ℕ} (h : o < (objs D).length) : (obAt D o).1 = 0 ↔ o < D.1.length := by
  constructor
  · intro h0
    rcases mem_objs.1 (obAt_mem h) with h' | h'
    · have h2 : obAt D o = obAt D (obAt D o).2.1 := by
        rw [obAt_of_lt h'.2.1]; exact Prod.ext h'.1 (Prod.ext rfl h'.2.2)
      have h3 := obAt_inj hW h (by rw [length_objs]; omega) h2
      omega
    · omega
  · intro h0; rw [obAt_of_lt h0]

/-! ### Touches -/

/-- An object touches the nodes that hold the variables of its clause; an incidence (E, j) also
touches h(j). -/
theorem tchB_iff {a o : ℕ} : tchB g n D a o = true ↔
    (∃ l ∈ clOf D o, l.1 / qv g n = a) ∨ ((obAt D o).1 = 1 ∧ home g (obAt D o).2.2 = a) := by
  simp [tchB]

/-- An incidence (E, j) touches h(j). -/
theorem tchB_home {o : ℕ} (h1 : (obAt D o).1 = 1) : tchB g n D (home g (obAt D o).2.2) o = true :=
  tchB_iff.2 (Or.inr ⟨h1, rfl⟩)

/-- For g > 0, the node that holds the variable x < n is below g. -/
theorem div_qv_lt (hg : 0 < g) {x : ℕ} (hx : x < n) : x / qv g n < g := by
  have h1 := Nat.div_add_mod (n + g - 1) g
  have h2 := Nat.mod_lt (n + g - 1) hg
  unfold qv
  generalize (n + g - 1) / g = q at h1 ⊢
  have hq : 0 < q := by
    rcases Nat.eq_zero_or_pos q with rfl | h
    · simp at h1; omega
    · exact h
  rw [Nat.div_lt_iff_lt_mul hq]
  have h3 : g * q = q * g := Nat.mul_comm _ _
  omega

/-- For g > 0 and well-formed data (WfD), a node that an object touches is below g. -/
theorem tch_lt (hg : 0 < g) (hW : WfD k n D) {o a : ℕ} (ho : o < (objs D).length) (h : tchB g n D a o = true) : a < g := by
  rcases tchB_iff.1 h with ⟨l, hl, rfl⟩ | ⟨_, rfl⟩
  · exact div_qv_lt hg ((clOf_wf hW ho).2.2 l hl)
  · exact Nat.mod_lt _ hg

/-- For g > 0 and well-formed data (WfD), every object touches a node below g. -/
theorem exists_tch (hg : 0 < g) (hW : WfD k n D) {o : ℕ} (ho : o < (objs D).length) : ∃ a < g, tchB g n D a o = true := by
  obtain ⟨l, hl⟩ := List.exists_mem_of_ne_nil _ (clOf_wf hW ho).1
  exact ⟨l.1 / qv g n, div_qv_lt hg ((clOf_wf hW ho).2.2 l hl), tchB_iff.2 (Or.inl ⟨l, hl, rfl⟩)⟩

/-- The object o touches at most (number of literals of its clause) + (kind of o) nodes below g.
With at most k literals (WfD) this gives the bound «at most k − 1 + κ tests» of Appendix D, Step 3
of the paper, which is not stated here. -/
theorem card_touched_le (o : ℕ) : ((Finset.range g).filter fun a => tchB g n D a o = true).card ≤ (clOf D o).length + (obAt D o).1 := by
  classical
  by_cases h1 : (obAt D o).1 = 1
  · have hsub : ((Finset.range g).filter fun a => tchB g n D a o = true) ⊆
        insert (home g (obAt D o).2.2) ((clOf D o).map fun l => l.1 / qv g n).toFinset := by
      intro a ha
      rcases tchB_iff.1 (Finset.mem_filter.1 ha).2 with ⟨l, hl, rfl⟩ | ⟨_, rfl⟩
      · exact Finset.mem_insert_of_mem (List.mem_toFinset.2 (List.mem_map.2 ⟨l, hl, rfl⟩))
      · exact Finset.mem_insert_self _ _
    refine (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans ?_)
    rw [h1]
    exact Nat.add_le_add_right ((List.toFinset_card_le _).trans (by simp)) 1
  · have hsub : ((Finset.range g).filter fun a => tchB g n D a o = true) ⊆ ((clOf D o).map fun l => l.1 / qv g n).toFinset := by
      intro a ha
      rcases tchB_iff.1 (Finset.mem_filter.1 ha).2 with ⟨l, hl, rfl⟩ | ⟨h, _⟩
      · exact List.mem_toFinset.2 (List.mem_map.2 ⟨l, hl, rfl⟩)
      · exact absurd h h1
    exact (Finset.card_le_card hsub).trans (((List.toFinset_card_le _).trans (by simp)).trans (Nat.le_add_right _ _))

end VariableBound.Net.Basic
