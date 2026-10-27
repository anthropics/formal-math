/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PrintedOrder.Defs
import SplitCount.Disjoint
import SplitCount.Tree
import SparsificationLemma.One
import Mathlib.Tactic

/-! # Section 7, proof of Corollary 6: «no two of which share a satisfying assignment, so that their numbers of satisfying assignments add up»

Proofs of `StAddUp`, `StCovered`, `StRootSame`, `StTreeAddsUp` and `StStepAdds` of
proof/consequences/PrintedOrder/Defs.lean.
* `stAddUp`: for every list of formulas. The assignments to x₀ … xₙ₋₁ that satisfy some formula of
  the list are the disjoint union of those that satisfy the first formula and those that satisfy
  some later one (`card_some`, by induction on the list).
* `stCovered`: an assignment satisfies a node of the tree exactly if it satisfies some leaf below
  it, by induction on the depth from the first half of `SplitCount.stDisjoint`.
* `stRootSame`: the formula at the root (clauses in a normal form, no clause twice, only the
  inclusion-minimal clauses) has the satisfying assignments of the given formula
  (`SparsificationLemma.sat_rootP`).
* `treeAddsUpFrom`, `stepAddsFrom`: the sums over the leaves and over the two children, from the
  statements named, which are hypotheses there; `stTreeAddsUp`, `stStepAdds`: the same on their
  proofs. -/

public section

namespace PrintedOrder

open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat SplitCount

open Classical in
/-- The number of satisfying assignments on n variables, written with `Holds`. -/
theorem cntN_eq (n : ℕ) (y : Fml) : cntN n y = (Finset.univ.filter fun b : Fin n → Bool => Holds (ext b) y).card := by
  unfold cntN Holds
  congr!

open Classical in
/-- If no assignment satisfies two formulas at different places of the list L, the number of
assignments to x₀ … xₙ₋₁ that satisfy some formula of L is the sum of the numbers of satisfying
assignments of the formulas of L. -/
theorem card_some (n : ℕ) : ∀ L : List Fml, (L.Pairwise fun y z => ∀ a : ℕ → Bool, ¬(Holds a y ∧ Holds a z)) →
    (Finset.univ.filter fun b : Fin n → Bool => ∃ y ∈ L, Holds (ext b) y).card = (L.map fun y => cntN n y).sum
  | [], _ => by simp
  | y :: L, hp => by
    have ih := card_some n L (List.pairwise_cons.1 hp).2
    have hd := (List.pairwise_cons.1 hp).1
    have e : (Finset.univ.filter fun b : Fin n → Bool => ∃ z ∈ y :: L, Holds (ext b) z) =
        (Finset.univ.filter fun b : Fin n → Bool => Holds (ext b) y) ∪ (Finset.univ.filter fun b : Fin n → Bool => ∃ z ∈ L, Holds (ext b) z) := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, List.mem_cons, exists_eq_or_imp]
    rw [e, Finset.card_union_of_disjoint, ih, List.map_cons, List.sum_cons, cntN_eq]
    exact Finset.disjoint_filter.2 fun b _ h1 ⟨z, hz, h2⟩ => hd z hz (ext b) ⟨h1, h2⟩

/-- **«no two of which share a satisfying assignment, so that their numbers of satisfying
assignments add up»**, for every formula ψ and every list L of formulas, on n variables: if no
assignment satisfies two formulas at different places of L, and an assignment satisfies ψ exactly if
it satisfies some formula of L, then the number of satisfying assignments of ψ is the sum of those
of the formulas of L. -/
theorem stAddUp : StAddUp := by
  classical
  intro n ψ L hp hc
  rw [← card_some n L hp, cntN_eq]
  exact congrArg Finset.card (Finset.filter_congr fun b _ => hc (ext b))

/-- An assignment satisfies a node of the counting tree exactly if it satisfies some leaf below it,
at every depth of the cut. By induction on the depth, from the first half of
`SplitCount.stDisjoint`. -/
theorem stCovered : StCovered := by
  intro θ k d
  induction d with
  | zero => intro x a; simp [leaves]
  | succ d ih =>
    intro x a
    cases h0 : stepC θ k x with
    | none => simp [leaves, h0]
    | some lh =>
      have el : leaves (stepC θ k) (d + 1) x = leaves (stepC θ k) d lh.1 ++ leaves (stepC θ k) d lh.2 := by simp [leaves, h0]
      have h1 : Holds a (leafF x) ↔ Holds a (leafF lh.1) ∨ Holds a (leafF lh.2) := (stDisjoint θ k x lh.1 lh.2 h0 a).1
      rw [el, h1, ih lh.1 a, ih lh.2 a]
      simp only [List.mem_append, or_and_right, exists_or]

/-- The formula at the root (with the empty side list) has the satisfying assignments of the given
formula. -/
theorem stRootSame : StRootSame := by
  intro u ψ a
  have h : Holds a (rootP ψ) ↔ Holds a ψ := SparsificationLemma.sat_rootP a ψ
  have e : leafF (rootPlain (u, ψ)).2 = rootP ψ := by simp [leafF, rootPlain]
  rw [e]
  exact h

/-- **The numbers of the leaves add up to that of the given formula**, from four statements taken as
hypotheses: no two leaves share a satisfying assignment (`SplitCount.StDisjointLeaves`); an
assignment satisfies a node exactly if it satisfies some leaf below it (`StCovered`); the root has
the satisfying assignments of the given formula (`StRootSame`); then the numbers add up (`StAddUp`). -/
theorem treeAddsUpFrom : SplitCount.StDisjointLeaves → StCovered → StRootSame → StAddUp → StTreeAddsUp := by
  intro hD hC hR hA θ k d n ψ
  have cP : ∀ y : CNode, stepPlain (stepC θ k) (List.replicate n (), y) =
      (stepC θ k y).map fun lh => ((List.replicate n (), lh.1), (List.replicate n (), lh.2)) := fun _ => rfl
  have hP : rootPlain (List.replicate n (), ψ) = (List.replicate n (), ((rootP ψ, []) : CNode)) := rfl
  have key := hA n ψ ((leaves (stepC θ k) d (rootP ψ, [])).map leafF) (List.pairwise_map.2 (hD θ k d _)) fun a => by
    rw [← hR (List.replicate n ()) ψ a]
    refine (hC θ k d _ a).trans ⟨fun ⟨y, hy, h⟩ => ⟨leafF y, List.mem_map_of_mem hy, h⟩, fun ⟨z, hz, h⟩ => ?_⟩
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
    exact ⟨y, hy, h⟩
  rw [hP, leaves_map (f := Prod.mk (List.replicate n ())) cP, List.map_map, key, List.map_map]
  rfl

/-- **The numbers of the leaves add up to that of the given formula**, for all thresholds, every
width and every depth of the cut: `treeAddsUpFrom` on the proofs of its four hypotheses. -/
theorem stTreeAddsUp : StTreeAddsUp := treeAddsUpFrom stDisjointLeaves stCovered stRootSame stAddUp

/-- The same for one step of the tree, from two statements taken as hypotheses: the two children of
a node share no satisfying assignment and an assignment satisfies the node exactly if it satisfies
one of them (`SplitCount.StDisjoint`); then the numbers add up (`StAddUp`, for the list of the two
children). -/
theorem stepAddsFrom : SplitCount.StDisjoint → StAddUp → StStepAdds := by
  intro hD hA θ k n x l h hst
  have h1 : ∀ a : ℕ → Bool, Holds a (leafF x) ↔ Holds a (leafF l) ∨ Holds a (leafF h) := fun a => (hD θ k x l h hst a).1
  have key := hA n (leafF x) [leafF l, leafF h]
    (List.Pairwise.cons (fun z hz a => by rw [List.mem_singleton.1 hz]; exact (hD θ k x l h hst a).2) (List.pairwise_singleton _ _))
    fun a => (h1 a).trans (by simp)
  simpa using key

/-- The number of satisfying assignments of a node is the sum of those of its two children:
`stepAddsFrom` on the proofs of its two hypotheses. -/
theorem stStepAdds : StStepAdds := stepAddsFrom stDisjoint stAddUp

end PrintedOrder
