/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachines.Math.SparsifyList
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Ring
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Nodup

/-! The branching tree of the sparsification lemma of Impagliazzo, Paturi and Zane (compare Lemma 4
of the paper; here with the thresholds of pickP) as plain functions on
List (List (ℕ × Bool)), written with list primitives only (filter, map, all, any, elem, find?, take,
dedup, …), so that
they can be proved polynomial-time piece by piece. At a node that is not a leaf, pickP finds a
clause H and clauses P₁, …, P_r such that every H ∪ Pᵢ is a clause of the node; one child adds H,
the other adds P₁, …, P_r.
The step takes the first applicable literal among the formula's own literals. The lemmas here show
that redP agrees with redLL and that the root rootP ψ satisfies the invariant NodeP. -/

namespace Groundwork.Sparsify

open Finset

/-- A literal: (variable, the value that makes it true). -/
public abbrev PLit : Type := ℕ × Bool
/-- A clause. -/
public abbrev PCl : Type := List PLit
/-- A formula. -/
public abbrev PFml : Type := List PCl

/-- Every literal of D is in C. -/
@[expose] public def subP (D C : PCl) : Bool := D.all fun a => C.elem a

/-- The clauses of length i that contain all of S. -/
@[expose] public def overP (s : PFml) (i : ℕ) (S : PCl) : PFml := s.filter fun C => decide (C.length = i) && subP S C

/-- Put A in front and drop the clauses that contain a member of A. -/
@[expose] public def addP (A s : PFml) : PFml := A ++ s.filter fun C => !(A.any fun D => subP D C)

/-- The inclusion-minimal clauses. -/
@[expose] public def redP (s : PFml) : PFml := s.filter fun C => s.all fun D => !(subP D C) || subP C D

/-- C without the literals of H. -/
@[expose] public def minusP (H C : PCl) : PCl := C.filter fun a => !(H.elem a)

/-- The literals of a formula, each once. -/
@[expose] public def litsOf (s : PFml) : PCl := (s.flatMap id).dedup

/-- The literals of C in the order of ls, each once. -/
@[expose] public def canonP (ls C : PCl) : PCl := ls.filter fun a => C.elem a

/-- The root: clauses in a normal form, no clause twice, inclusion-minimal clauses only. -/
@[expose] public def rootP (φ : PFml) : PFml := redP ((φ.map fun C => canonP (litsOf φ) C).dedup)

/-- At most k times: the first clause of l that has no literal used so far. -/
@[expose] public def greedyP : ℕ → PCl → PFml → PFml
  | 0, _, _ => []
  | k + 1, used, l =>
    match l.find? fun Q => Q.all fun a => !(used.elem a) with
    | none => []
    | some Q => Q :: greedyP k (used ++ Q) l

/-- The first applicable of three rules, as a clause H and clauses P₁, …, P_r.
Rule 1: a literal a lies in at least τ clauses of length 2; H = [a].
Rule 2: two different literals a, b lie together in at least τ clauses of length 3; H = [a, b].
In both, the Pᵢ are the first τ of these clauses without the literals of H.
Rule 3: a literal a lies in at least 2τ³ clauses of length 3; H = [a], and the Pᵢ are at most τ² of
these clauses
without a, pairwise disjoint, chosen greedily. -/
@[expose] public def pickP (τ : ℕ) (s : PFml) : Option (PCl × PFml) :=
  match (litsOf s).find? fun a => decide (τ ≤ (overP s 2 [a]).length) with
  | some a => some ([a], ((overP s 2 [a]).take τ).map (minusP [a]))
  | none =>
    match (List.product (litsOf s) (litsOf s)).find? fun ab =>
        !(ab.1 == ab.2) && decide (τ ≤ (overP s 3 [ab.1, ab.2]).length) with
    | some ab => some ([ab.1, ab.2], ((overP s 3 [ab.1, ab.2]).take τ).map (minusP [ab.1, ab.2]))
    | none =>
      match (litsOf s).find? fun a => decide (2 * τ ^ 3 ≤ (overP s 3 [a]).length) with
      | some a => some ([a], greedyP (τ ^ 2) [] ((overP s 3 [a]).map (minusP [a])))
      | none => none

/-- The light child (H added) and the heavy child (P₁, …, P_r added), with H and the Pᵢ of pickP;
none at a leaf. -/
@[expose] public def stepP (τ : ℕ) (s : PFml) : Option (PFml × PFml) :=
  (pickP τ s).map fun HP => (addP [HP.1] s, addP HP.2 s)

section Eq

theorem subP_iff (D C : PCl) : subP D C = true ↔ ∀ a ∈ D, a ∈ C := by simp [subP]

theorem redP_eq (s : PFml) : redP s = redLL s := by
  rw [redP, redLL]
  apply List.filter_congr
  intro C _
  rw [Bool.eq_iff_iff]
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq]
  refine forall₂_congr fun D _ => ?_
  rw [← Bool.not_eq_true, subP_iff, subP_iff]
  tauto

theorem mem_litsOf {s : PFml} {C : PCl} (hC : C ∈ s) {a : PLit} (ha : a ∈ C) : a ∈ litsOf s := by
  simp only [litsOf, List.mem_dedup, List.mem_flatMap, id]
  exact ⟨C, hC, ha⟩

end Eq

section Main

/-- The clauses as finite sets. -/
abbrev toF (s : PFml) : List (Finset PLit) := s.map List.toFinset

/-- The invariant of the walk: no literal twice in a clause, and a node of the tree of ψ. -/
def NodeP (τ : ℕ) (ψ s : PFml) (p q : ℕ) : Prop := (∀ C ∈ s, C.Nodup) ∧ NodeL τ (toF ψ) (toF s) p q

variable {τ n : ℕ} {ψ s l h : PFml} {p q : ℕ}

theorem toFinset_canonP {C : PCl} (hC : C ∈ ψ) : (canonP (litsOf ψ) C).toFinset = C.toFinset := by
  ext a
  simp only [canonP, List.mem_toFinset, List.mem_filter, List.elem_eq_mem, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨mem_litsOf hC h, h⟩⟩

theorem toFinset_rootP (ψ : PFml) : (toF (rootP ψ)).toFinset = red (toF ψ).toFinset := by
  rw [rootP, redP_eq, toF, map_redLL, toFinset_redL]
  congr 1
  ext X
  simp only [List.mem_toFinset, List.mem_map, List.mem_dedup]
  constructor
  · rintro ⟨Y, ⟨C, hC, rfl⟩, rfl⟩
    exact ⟨C, hC, (toFinset_canonP hC).symm⟩
  · rintro ⟨C, hC, rfl⟩
    exact ⟨_, ⟨C, hC, rfl⟩, toFinset_canonP hC⟩

theorem nodeP_root (τ : ℕ) (ψ : PFml) : NodeP τ ψ (rootP ψ) 0 0 := by
  have hmem : ∀ X ∈ rootP ψ, ∃ C ∈ ψ, X = canonP (litsOf ψ) C := by
    intro X hX
    obtain ⟨C, hC, rfl⟩ := List.mem_map.1 (List.mem_dedup.1 (List.mem_filter.1 hX).1)
    exact ⟨C, hC, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro X hX
    obtain ⟨C, -, rfl⟩ := hmem X hX
    exact (List.nodup_dedup _).filter _
  · refine List.Nodup.map_on ?_ ((List.nodup_dedup _).filter _)
    intro X hX Y hY hXY
    obtain ⟨C, hC, rfl⟩ := hmem X hX
    obtain ⟨D, hD, rfl⟩ := hmem Y hY
    rw [toFinset_canonP hC, toFinset_canonP hD] at hXY
    apply List.filter_congr
    intro a _
    have := Finset.ext_iff.1 hXY a
    simp only [List.mem_toFinset] at this
    simp only [List.elem_eq_mem, this]
  · rw [toFinset_rootP]
    exact node_root τ _

end Main

end Groundwork.Sparsify
