/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsificationLemma.Defs
import all CountKSat.StepCount
import SparsifyWidthK.ProgMain
import all SparsifyWidthK.Refine
import all CountKSatRate.Leaf
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Tauto

/-! # Every assignment that satisfies ψ satisfies exactly one output

This file proves three statements of proof/sparsification/SparsificationLemma/Defs.lean:
`StExactlyOne`, `StCountOfExactlyOne` and `StNoTaut`.

* One branching (`sat_first`, `sat_second`). An assignment satisfies the first child exactly if it
  satisfies the node and makes a literal of H true. It satisfies the second child exactly
  if it satisfies the node and makes no literal of H true: then every clause E ⊇ H has its true
  literal in E ∖ H.
* The tree (`countP_leaves`). By induction on the depth: below a node whose side clauses have one
  literal each, the number of positions in the list of outputs that b satisfies is 1 if b satisfies
  the node, and 0 otherwise. At the root the node has the satisfying assignments of ψ (`sat_rootP`).
* `exactlyOne_iff_countP` says that `ExactlyOne b ψ Φ` holds exactly if this number is 1 when b
  satisfies ψ and 0 otherwise. `stCountOfExactlyOne` adds these numbers up over all assignments to n
  variables.
* `stNoTaut`: every assignment satisfies a clause that contains a variable together with its
  negation, so deleting such clauses changes nothing.

The facts on one step come from proof/consequences/CountKSat/StepCount.lean. -/

public section

namespace SparsificationLemma

open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate
open CountKSat.StepCount

/-! ### Satisfying a formula -/

/-- Whether b satisfies ψ can be computed. -/
instance instDecidableSat (b : ℕ → Bool) (ψ : PFml) : Decidable (Sat b ψ) := by unfold Sat; infer_instance

/-- b satisfies a formula in two parts exactly if it satisfies both parts. -/
theorem sat_append (b : ℕ → Bool) (x y : PFml) : Sat b (x ++ y) ↔ Sat b x ∧ Sat b y := holds_append _ x y

/-- b satisfies `addP A s` exactly if it satisfies A and s: a clause that `addP` deletes contains a
clause of A. -/
theorem sat_addP (b : ℕ → Bool) (A s : PFml) : Sat b (addP A s) ↔ Sat b A ∧ Sat b s := holds_addP _ A s

/-- Deleting the clauses that contain another clause does not change the satisfying assignments. -/
theorem sat_rootP (b : ℕ → Bool) (ψ : PFml) : Sat b (rootP ψ) ↔ Sat b ψ :=
  (ProgMain.sat_toFin (fun l : PLit => b l.1 = l.2) (rootP ψ)).symm.trans
    (Iff.trans (by rw [Refine.toFin_rootP, sat_red]) (ProgMain.sat_toFin (fun l : PLit => b l.1 = l.2) ψ))

/-- If every side clause has one literal, `leafM x` has the satisfying assignments of `leafF x`: it
only lacks the repetitions in the side list. -/
theorem sat_leafM (b : ℕ → Bool) {x : CNode} (hx : ∀ C ∈ x.2, ∃ l, C = [l]) : Sat b (leafM x) ↔ Sat b (leafF x) :=
  Leaf.sat_leafM_iff (n := 0) (fun C hC => Or.inr (hx C hC)) b

/-- Writing every clause once does not change the satisfying assignments. -/
theorem sat_out (b : ℕ → Bool) (x : CNode) : Sat b (out x) ↔ Sat b (leafM x) := by
  simp only [Sat, out, List.mem_dedup]

/-- If every side clause has one literal, the output `out x` has the satisfying assignments of
`leafF x`. -/
theorem sat_out_iff (b : ℕ → Bool) {x : CNode} (hx : ∀ C ∈ x.2, ∃ l, C = [l]) : Sat b (out x) ↔ Sat b (leafF x) :=
  (sat_out b x).trans (sat_leafM b hx)

/-! ### One branching -/

/-- The two children of a node at which the rule picks H, with P the list of the E ∖ H. -/
theorem stepC_of_pickK {θ : ℕ → ℕ} {k : ℕ} {x : CNode} {H : PCl} {P : PFml} (hp : pickK θ k x.1 = some (H, P)) :
    stepC θ k x = some ((addP [H] x.1, x.2), (addP P x.1, negU H ++ x.2)) := by simp [stepC, hp]

/-- b satisfies the first child exactly if it satisfies the node and makes a literal of H true. -/
theorem sat_first (b : ℕ → Bool) (x : CNode) (H : PCl) :
    Sat b (leafF (addP [H] x.1, x.2)) ↔ Sat b (leafF x) ∧ ∃ ω ∈ H, b ω.1 = ω.2 := by
  have h := holds_singleton (fun l : PLit => b l.1 = l.2) H
  change Sat b [H] ↔ _ at h
  simp only [leafF, sat_append, sat_addP, h]
  tauto

/-- b satisfies the second child exactly if it satisfies the node and makes no literal of H true. -/
theorem sat_second {θ : ℕ → ℕ} {k : ℕ} {x : CNode} {H : PCl} {P : PFml} (hp : pickK θ k x.1 = some (H, P)) (b : ℕ → Bool) :
    Sat b (leafF (addP P x.1, negU H ++ x.2)) ↔ Sat b (leafF x) ∧ ¬ ∃ ω ∈ H, b ω.1 = ω.2 := by
  have h := holds_negU b H
  change Sat b (negU H) ↔ _ at h
  simp only [leafF, sat_append, sat_addP, h]
  exact ⟨fun ⟨⟨h1, h2⟩, _, h4⟩ => ⟨⟨h2, h4⟩, h1⟩, fun ⟨⟨h2, h4⟩, h1⟩ => ⟨⟨h1, h2⟩, holds_petals (pickK_petals hp) h1 h4, h4⟩⟩

/-! ### The number of positions of a list that b satisfies -/

/-- The number of entries of a list with p is the number of positions whose entry has p. -/
theorem countP_eq_card {α : Type} (p : α → Bool) (l : List α) : l.countP p = (univ.filter fun i : Fin l.length => p (l.get i) = true).card := by
  have h : l.countP p = (l.map fun a => if p a = true then 1 else 0).sum := by
    induction l with
    | nil => rfl
    | cons a l ih => by_cases h : p a = true <;> simp [h, ih, add_comm]
  rw [h, ← Fin.sum_univ_fun_getElem, Finset.card_filter]
  rfl

/-- `ExactlyOne b ψ Φ` says that the number of positions of Φ that b satisfies is 1 if b satisfies
ψ, and 0 otherwise. -/
theorem exactlyOne_iff_countP (b : ℕ → Bool) (ψ : PFml) (Φ : List PFml) :
    ExactlyOne b ψ Φ ↔ Φ.countP (fun Ψ => decide (Sat b Ψ)) = if Sat b ψ then 1 else 0 := by
  by_cases hψ : Sat b ψ
  · simp only [ExactlyOne, hψ, if_true, not_true_eq_false, false_imp_iff, and_true, true_imp_iff]
    rw [countP_eq_card, Finset.card_eq_one, Finset.singleton_iff_unique_mem]
    simp
  · simp only [ExactlyOne, hψ, if_false, not_false_eq_true, false_imp_iff, true_and, true_imp_iff]
    rw [List.countP_eq_zero]
    simp

/-- Below a node whose side clauses have one literal each, b satisfies one position of the list of
outputs if it satisfies the node, and none otherwise. -/
theorem countP_leaves (θ : ℕ → ℕ) (k D : ℕ) (b : ℕ → Bool) (x : CNode) (hx : ∀ C ∈ x.2, ∃ l, C = [l]) :
    ((leaves (stepC θ k) D x).map out).countP (fun Ψ => decide (Sat b Ψ)) = if Sat b (leafF x) then 1 else 0 := by
  have h0 : ∀ x : CNode, (∀ C ∈ x.2, ∃ l, C = [l]) → ([x].map out).countP (fun Ψ => decide (Sat b Ψ)) = if Sat b (leafF x) then 1 else 0 := by
    intro x hx
    simp [List.countP_cons, sat_out_iff b hx]
  induction D generalizing x with
  | zero => exact h0 x hx
  | succ D ih =>
    cases hp : pickK θ k x.1 with
    | none =>
      have hst : stepC θ k x = none := by simp [stepC, hp]
      simp only [leaves, hst]
      exact h0 x hx
    | some HP =>
      obtain ⟨H, P⟩ := HP
      have hx2 : ∀ C ∈ negU H ++ x.2, ∃ l, C = [l] := by
        intro C hC
        rcases List.mem_append.1 hC with hC | hC
        · obtain ⟨l, -, rfl⟩ := List.mem_map.1 hC
          exact ⟨_, rfl⟩
        · exact hx C hC
      simp only [leaves, stepC_of_pickK hp, List.map_append, List.countP_append]
      rw [ih (addP [H] x.1, x.2) hx, ih (addP P x.1, negU H ++ x.2) hx2]
      simp only [sat_first, sat_second hp]
      by_cases h1 : Sat b (leafF x) <;> by_cases h2 : ∃ ω ∈ H, b ω.1 = ω.2 <;> simp [h1, h2]

/-- The number of outputs (positions of the list) that b satisfies is 1 if b satisfies ψ, and 0
otherwise. -/
theorem countP_outputs (θ : ℕ → ℕ) (k D : ℕ) (ψ : PFml) (b : ℕ → Bool) :
    (outputs θ k D ψ).countP (fun Ψ => decide (Sat b Ψ)) = if Sat b ψ then 1 else 0 := by
  have h : Sat b (leafF (root ψ)) ↔ Sat b ψ := by simp [leafF, root, sat_rootP]
  rw [outputs, tree, countP_leaves θ k D b (root ψ) (by simp [root])]
  simp only [h]

/-- Every assignment that satisfies ψ satisfies exactly one output, and every other assignment
satisfies none. -/
theorem stExactlyOne : StExactlyOne := fun θ k D ψ b => (exactlyOne_iff_countP b ψ _).2 (countP_outputs θ k D ψ b)

/-! ### The counts -/

/-- The number of satisfying assignments on n variables, as a sum of ones and zeros over the
assignments. -/
theorem cntN_eq_sum (n : ℕ) (x : PFml) : cntN n x = ∑ a : Fin n → Bool, if Sat (ext a) x then 1 else 0 := by
  rw [cntN, Finset.card_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr

/-- The sum of the counts of the formulas of Φ is the sum, over the assignments, of the number of
positions of Φ that the assignment satisfies. -/
theorem sum_cntN (n : ℕ) (Φ : List PFml) : (Φ.map (cntN n)).sum = ∑ a : Fin n → Bool, Φ.countP fun Ψ => decide (Sat (ext a) Ψ) := by
  induction Φ with
  | nil => simp
  | cons Ψ Φ ih => simp [List.countP_cons, Finset.sum_add_distrib, ih, cntN_eq_sum, add_comm]

/-- If every assignment satisfies exactly one formula of Φ or none, according to whether it
satisfies ψ, the count of ψ is the sum of the counts of the formulas of Φ. -/
theorem stCountOfExactlyOne : StCountOfExactlyOne := by
  intro n ψ Φ h
  rw [sum_cntN, cntN_eq_sum]
  exact Finset.sum_congr rfl fun a _ => ((exactlyOne_iff_countP (ext a) ψ Φ).1 (h (ext a))).symm

/-! ### Clauses that contain a variable together with its negation -/

/-- Deleting the clauses that contain a variable together with its negation: every assignment
satisfies such a clause. -/
theorem stNoTaut : StNoTaut := by
  intro ψ
  refine ⟨fun b => ⟨fun h C hC => ?_, fun h C hC => h C (List.mem_filter.1 hC).1⟩, fun k n h C hC => h C (List.mem_filter.1 hC).1, fun C hC l hl hn => ?_⟩
  · by_cases ht : (C.any fun l => C.contains (l.1, !l.2)) = true
    · obtain ⟨l, hl, hc⟩ := List.any_eq_true.1 ht
      have hc' : (l.1, !l.2) ∈ C := by simpa using hc
      by_cases hb : b l.1 = l.2
      · exact ⟨l, hl, hb⟩
      · exact ⟨(l.1, !l.2), hc', by revert hb; cases b l.1 <;> cases l.2 <;> simp⟩
    · exact h C (List.mem_filter.2 ⟨hC, by simpa using ht⟩)
  · have h : (!(C.any fun l => C.contains (l.1, !l.2))) = true := (List.mem_filter.1 hC).2
    have h2 : (C.any fun l => C.contains (l.1, !l.2)) = true := List.any_eq_true.2 ⟨l, hl, by simpa using hn⟩
    rw [h2] at h
    exact absurd h (by decide)

end SparsificationLemma
