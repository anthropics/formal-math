/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SplitCount.Defs
import Mathlib.Tactic.Tauto

/-! # Proof of Corollary 6: «no two of which share a satisfying assignment»

A node of the tree is a pair (s, X): the formula s that the branching rule looks at, and the side
list X. What is counted at it is X ++ s (`leafF`). The light child gets the heart H as a clause; the
heavy child gets the petals, and on its side list one unit clause per literal of H, saying that the
literal is false (`negU H`).
* `holds_light`, `holds_heavy`: an assignment satisfies the light child exactly if it satisfies the
  node and makes a literal of H true, and the heavy child exactly if it satisfies the node and makes
  no literal of H true.
* `stDisjoint`: so it satisfies the node exactly if it satisfies one of the children, and never
  both.
* `stDisjointLeaves`: no assignment satisfies two different leaves: by induction on the depth; an
  assignment that satisfies a leaf satisfies every node above it (`holds_of_leaf`).
The facts on `addP`, `negU` and `pickK` are proved, as private theorems that an importing file
cannot use and for truth values in place of assignments, in
proof/consequences/CountKSat/StepCount.lean. -/

public section

namespace SplitCount

open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog CountKSat Eight.Width

/-- `addP A s` holds exactly if A and s hold: a clause that `addP` drops contains a clause of A. -/
theorem holds_addP (b : ℕ → Bool) (A s : PFml) : Holds b (addP A s) ↔ Holds b A ∧ Holds b s := by
  rw [addP, holds_append]
  refine and_congr_right fun hA => ⟨fun h C hC => ?_, fun h C hC => h C (List.mem_filter.1 hC).1⟩
  by_cases hd : (A.any fun D => subP D C) = true
  · obtain ⟨D, hD, hDC⟩ := List.any_eq_true.1 hd
    obtain ⟨l, hl, hv⟩ := hA D hD
    have hsub : ∀ a ∈ D, a ∈ C := by simpa [subP] using hDC
    exact ⟨l, hsub l hl, hv⟩
  · exact h C (List.mem_filter.2 ⟨hC, by simpa using hd⟩)

/-- A formula with the one clause H holds exactly if a literal of H is true. -/
theorem holds_singleton (b : ℕ → Bool) (H : PCl) : Holds b [H] ↔ ∃ l ∈ H, b l.1 = l.2 := by simp [Holds]

/-- The unit clauses `negU H` hold under an assignment b exactly if b makes no literal of H true. -/
theorem holds_negU (b : ℕ → Bool) (H : PCl) : Holds b (negU H) ↔ ¬ ∃ l ∈ H, b l.1 = l.2 := by
  simp only [Holds, negU, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, List.mem_singleton, exists_eq_left,
    not_exists, not_and]
  refine forall₂_congr fun l _ => ?_
  cases b l.1 <;> cases l.2 <;> simp

/-- If no literal of the heart H is true and s holds, then the petals hold. -/
theorem holds_petals {b : ℕ → Bool} {s P : PFml} {H : PCl} (hP : ∀ Q ∈ P, ∃ C ∈ s, ∀ l ∈ C, l ∈ H ∨ l ∈ Q)
    (hH : ¬ ∃ l ∈ H, b l.1 = l.2) (hs : Holds b s) : Holds b P := by
  intro Q hQ
  obtain ⟨C, hC, hCQ⟩ := hP Q hQ
  obtain ⟨l, hl, hv⟩ := hs C hC
  rcases hCQ l hl with h | h
  · exact absurd ⟨l, h, hv⟩ hH
  · exact ⟨l, h, hv⟩

/-- Every petal Q that `pickK` returns comes from a clause of s whose literals lie in the heart or
in Q. -/
theorem pickK_petals {θ : ℕ → ℕ} {k : ℕ} {s : PFml} {H : PCl} {P : PFml} (h : pickK θ k s = some (H, P)) :
    ∀ Q ∈ P, ∃ C ∈ s, ∀ l ∈ C, l ∈ H ∨ l ∈ Q := by
  have hmem : (H, P) ∈ (pairsK k).filterMap (tryP θ k s) := List.mem_of_head? h
  obtain ⟨jh, -, htry⟩ := List.mem_filterMap.1 hmem
  obtain ⟨H', -, he⟩ := Option.map_eq_some_iff.1 htry
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  intro Q hQ
  obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hQ
  refine ⟨C, (List.mem_filter.1 hC).1, fun l hl => ?_⟩
  by_cases hlH : l ∈ H'
  · exact Or.inl hlH
  · exact Or.inr (List.mem_filter.2 ⟨hl, by simpa using hlH⟩)

/-- An assignment satisfies the light child exactly if it satisfies the node and makes a literal of
the heart true. -/
theorem holds_light (b : ℕ → Bool) (x : CNode) (H : PCl) :
    Holds b (leafF (addP [H] x.1, x.2)) ↔ Holds b (leafF x) ∧ ∃ l ∈ H, b l.1 = l.2 := by
  simp only [leafF]
  rw [holds_append, holds_append, holds_addP, holds_singleton]
  tauto

/-- An assignment satisfies the heavy child exactly if it satisfies the node and makes no literal of
the heart true. -/
theorem holds_heavy (b : ℕ → Bool) (x : CNode) (H : PCl) (P : PFml) (hP : ∀ Q ∈ P, ∃ C ∈ x.1, ∀ l ∈ C, l ∈ H ∨ l ∈ Q) :
    Holds b (leafF (addP P x.1, negU H ++ x.2)) ↔ Holds b (leafF x) ∧ ¬ ∃ l ∈ H, b l.1 = l.2 := by
  simp only [leafF]
  rw [holds_append, holds_append, holds_append, holds_addP, holds_negU]
  constructor
  · rintro ⟨⟨h1, h2⟩, -, h4⟩
    exact ⟨⟨h2, h4⟩, h1⟩
  · rintro ⟨⟨h2, h4⟩, h1⟩
    exact ⟨⟨h1, h2⟩, holds_petals hP h1 h4, h4⟩

/-- «no two of which share a satisfying assignment», at one node: an assignment satisfies the node
exactly if it satisfies one of the two children, and it never satisfies both. -/
theorem stDisjoint : StDisjoint := by
  intro θ k x l h hst a
  obtain ⟨⟨H, P⟩, hp, he⟩ := Option.map_eq_some_iff.1 hst
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  have hL := holds_light a x H
  have hR := holds_heavy a x H P (pickK_petals hp)
  constructor
  · change Holds a _ ↔ Holds a _ ∨ Holds a _
    rw [hL, hR]
    constructor
    · intro hx
      by_cases hH : ∃ l ∈ H, a l.1 = l.2
      · exact Or.inl ⟨hx, hH⟩
      · exact Or.inr ⟨hx, hH⟩
    · rintro (h | h) <;> exact h.1
  · change ¬ (Holds a _ ∧ Holds a _)
    rw [hL, hR]
    rintro ⟨h1, h2⟩
    exact h2.2 h1.2

/-- An assignment that satisfies a leaf of the tree below x satisfies x. -/
theorem holds_of_leaf (θ : ℕ → ℕ) (k : ℕ) (a : ℕ → Bool) : ∀ (d : ℕ) (x y : CNode), y ∈ leaves (stepC θ k) d x →
    (∀ C ∈ leafF y, ∃ t ∈ C, a t.1 = t.2) → ∀ C ∈ leafF x, ∃ t ∈ C, a t.1 = t.2 := by
  intro d
  induction d with
  | zero =>
    intro x y hy h
    have : y = x := by simpa [leaves] using hy
    rwa [this] at h
  | succ d ih =>
    intro x y hy h
    cases h0 : stepC θ k x with
    | none =>
      have : y = x := by simpa [leaves, h0] using hy
      rwa [this] at h
    | some lh =>
      have el : leaves (stepC θ k) (d + 1) x = leaves (stepC θ k) d lh.1 ++ leaves (stepC θ k) d lh.2 := by simp [leaves, h0]
      rw [el] at hy
      have hd := (stDisjoint θ k x lh.1 lh.2 h0 a).1
      rcases List.mem_append.1 hy with hy | hy
      · exact hd.2 (Or.inl (ih _ y hy h))
      · exact hd.2 (Or.inr (ih _ y hy h))

/-- «no two of which share a satisfying assignment», for the outputs: no assignment satisfies the
formulas of two different leaves of the tree below any node, cut at any depth. -/
theorem stDisjointLeaves : StDisjointLeaves := by
  intro θ k d
  induction d with
  | zero => intro x; simp [leaves]
  | succ d ih =>
    intro x
    cases h0 : stepC θ k x with
    | none => simp [leaves, h0]
    | some lh =>
      have el : leaves (stepC θ k) (d + 1) x = leaves (stepC θ k) d lh.1 ++ leaves (stepC θ k) d lh.2 := by simp [leaves, h0]
      rw [el, List.pairwise_append]
      refine ⟨ih lh.1, ih lh.2, fun y hy z hz a hyz => ?_⟩
      exact (stDisjoint θ k x lh.1 lh.2 h0 a).2 ⟨holds_of_leaf θ k a d _ y hy hyz.1, holds_of_leaf θ k a d _ z hz hyz.2⟩

end SplitCount
