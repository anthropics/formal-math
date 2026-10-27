/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SplitCount.Defs
import SparsifyWidthK.Thresholds
import CountKSat.ProgC
import CountKSat.StepCount
import CountKSat.Walk
import Mathlib.Tactic.Tauto

/-! # Proof of Corollary 6, step 2

«their form of the Sparsification Lemma turns a k-CNF on n variables, for any ε > 0, into at most
2^{εn} k-CNFs on the same variables, each with O(n) clauses, no two of which share a satisfying
assignment, so that their numbers of satisfying assignments add up.»
The bounds on the tree are those of proof/consequences/CountKSat/ (`CountKSat.SparsifiesC`, given by
`CountKSat.stProgC` at the thresholds of `WidthK.stExistsTau`), whose root carries the clauses xᵢ ∨
¬xᵢ on its side list. They are carried over to the tree of this folder, whose side list starts empty
and whose nodes carry n in unary:
* `leaves_map`, `round_iterate_map`: if a map f of nodes commutes with two step functions, the
  leaves and the stacks of the walk from f x are the images of those from x;
* `stepC_withSide`: the step `stepC` only puts clauses in front of the side list and never reads it,
  so it commutes with appending t to the side list (`withSide t`); `stepPlain` commutes with putting
  n beside the node, by definition;
* `cntN_withSide`: the clauses xᵢ ∨ ¬xᵢ are always true, so they do not change the number of
  satisfying assignments.
The result is `sparsifiesPlain_of` and `stStepTwo`. -/

public section

namespace SplitCount

open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK.Prog CountKSat Eight Eight.Width

section maps

variable {σ ρ : Type} {s₁ : σ → Option (σ × σ)} {s₂ : ρ → Option (ρ × ρ)} {f : σ → ρ}

/-- If f commutes with the step functions, the leaves below f x are the images of the leaves below
x. -/
theorem leaves_map (h : ∀ x, s₂ (f x) = (s₁ x).map fun lh => (f lh.1, f lh.2)) (d : ℕ) (x : σ) : leaves s₂ d (f x) = (leaves s₁ d x).map f := by
  induction d generalizing x with
  | zero => simp [leaves]
  | succ d ih =>
    cases h0 : s₁ x with
    | none =>
      have h1 : s₂ (f x) = none := by rw [h, h0]; rfl
      simp [leaves, h0, h1]
    | some lh =>
      have h1 : s₂ (f x) = some (f lh.1, f lh.2) := by rw [h, h0]; rfl
      simp [leaves, h0, h1, ih]

/-- If f commutes with the step functions, it commutes with one round of the walk. -/
theorem round_map (h : ∀ x, s₂ (f x) = (s₁ x).map fun lh => (f lh.1, f lh.2)) (p : List σ × List σ) :
    round s₂ (p.1.map f, p.2.map f) = ((round s₁ p).1.map f, (round s₁ p).2.map f) := by
  obtain ⟨st, out⟩ := p
  cases st with
  | nil => simp [Sparsify.round]
  | cons x r =>
    cases h0 : s₁ x with
    | none =>
      have h1 : s₂ (f x) = none := by rw [h, h0]; rfl
      simp [Sparsify.round, h0, h1]
    | some lh =>
      have h1 : s₂ (f x) = some (f lh.1, f lh.2) := by rw [h, h0]; rfl
      simp [Sparsify.round, h0, h1]

/-- If f commutes with the step functions, it commutes with any number of rounds of the walk. -/
theorem round_iterate_map (h : ∀ x, s₂ (f x) = (s₁ x).map fun lh => (f lh.1, f lh.2)) (i : ℕ) (p : List σ × List σ) :
    (round s₂)^[i] (p.1.map f, p.2.map f) = (((round s₁)^[i] p).1.map f, ((round s₁)^[i] p).2.map f) := by
  induction i generalizing p with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, round_map h, ih]

end maps

/-- The node x with the clauses t appended to its side list. -/
def withSide (t : PFml) (x : CNode) : CNode := (x.1, x.2 ++ t)

/-- The step of the tree only puts clauses in front of the side list and never reads it. -/
theorem stepC_withSide (θ : ℕ → ℕ) (k : ℕ) (t : PFml) (x : CNode) :
    stepC θ k (withSide t x) = (stepC θ k x).map fun lh => (withSide t lh.1, withSide t lh.2) := by
  cases h : pickK θ k x.1 <;> simp [stepC, withSide, h]

/-- The formula of a node is not longer than with clauses appended to the side list. -/
theorem length_leafF_le (t : PFml) (x : CNode) : (leafF x).length ≤ (leafF (withSide t x)).length := by
  simp only [leafF, withSide, List.length_append]
  omega

/-- A clause of the formula of a node is still there after clauses are appended to the side list. -/
theorem mem_leafF_withSide {t : PFml} {x : CNode} {C : PCl} (h : C ∈ leafF x) : C ∈ leafF (withSide t x) := by
  simp only [leafF, withSide, List.mem_append] at h ⊢
  tauto

/-- The clauses xᵢ ∨ ¬xᵢ on the side list do not change the number of satisfying assignments. -/
theorem cntN_withSide (n m : ℕ) (x : CNode) : cntN n (leafF (withSide (taut m) x)) = cntN n (leafF x) := by
  unfold cntN
  refine congrArg Finset.card (Finset.filter_congr fun v _ => ?_)
  change Holds (ext v) _ ↔ Holds (ext v) _
  simp only [leafF, withSide]
  rw [holds_append, holds_append, holds_append]
  have h1 : Holds (ext v) (taut m) := by
    intro C hC
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hC
    cases hb : ext v i
    · exact ⟨(i, false), by simp, hb⟩
    · exact ⟨(i, true), by simp, hb⟩
  tauto

/-- The bounds of proof/consequences/CountKSat/ on the tree whose root has the clauses xᵢ ∨ ¬xᵢ on
its side list hold for the tree whose side list starts empty and whose nodes carry n in unary. -/
theorem sparsifiesPlain_of {k : ℕ} {ε : ℝ} {θ : ℕ → ℕ} {Dd Bl Sk : ℕ} (h : SparsifiesC k ε (stepC θ k) Dd Bl Sk) : SparsifiesPlain k ε (stepC θ k) Dd Bl Sk := by
  intro n ψ hψ
  obtain ⟨t1, t2, t3, t4⟩ := h n ψ hψ
  obtain ⟨u, hu⟩ : ∃ u : List Unit, u = List.replicate n () := ⟨_, rfl⟩
  obtain ⟨r₀, hr₀⟩ : ∃ r₀ : CNode, r₀ = (rootP ψ, []) := ⟨_, rfl⟩
  have hC : rootC (List.replicate n (), ψ) = withSide (taut n) r₀ := by simp [rootC, withSide, hr₀]
  have hP : rootPlain (List.replicate n (), ψ) = (u, r₀) := by rw [hu, hr₀]; rfl
  have cC := stepC_withSide θ k (taut n)
  have cP : ∀ y : CNode, stepPlain (stepC θ k) (u, y) = (stepC θ k y).map fun lh => ((u, lh.1), (u, lh.2)) := fun _ => rfl
  rw [hC] at t1 t2 t3 t4
  rw [leaves_map cC] at t1 t2 t3
  rw [hP, leaves_map (f := Prod.mk u) cP]
  obtain ⟨L, hL⟩ : ∃ L, L = leaves (stepC θ k) (Dd * n) r₀ := ⟨_, rfl⟩
  rw [← hL] at t1 t2 t3 ⊢
  refine ⟨by simpa using t1, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨a1, a2, a3, -⟩ := t2 _ (List.mem_map_of_mem hy)
    refine ⟨?_, hu, (length_leafF_le _ y).trans a2, fun C hC => a3 C (mem_leafF_withSide hC)⟩
    rw [cC, Option.map_eq_none_iff] at a1
    rw [cP, a1]
    rfl
  · rw [t3, List.map_map, List.map_map]
    exact congrArg List.sum (List.map_congr_left fun y _ => cntN_withSide n n y)
  · intro i
    have eC := round_iterate_map cC i ([r₀], [])
    have eP := round_iterate_map (f := Prod.mk u) cP i ([r₀], [])
    obtain ⟨b1, b2⟩ := t4 i
    simp only [List.map_cons, List.map_nil] at eC eP
    rw [eC] at b1 b2
    rw [eP]
    refine ⟨by simpa using b1, fun x hx => ?_⟩
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
    obtain ⟨a2, a3⟩ := b2 _ (List.mem_map_of_mem hy)
    exact ⟨hu, (length_leafF_le _ y).trans a2, fun C hC => a3 C (mem_leafF_withSide hC)⟩

/-- **Step 2.** For every k and ε > 0 some threshold parameter τ gives a tree that sparsifies width
k for counting, from the root with the empty side list: the bounds of `CountKSat.stProgC` at the
thresholds of `WidthK.stExistsTau`, carried over by `sparsifiesPlain_of`. -/
theorem stStepTwo : StStepTwo := fun k _ hε => by
  obtain ⟨τ, -, h4, hτ⟩ := WidthK.stExistsTau k 0 _ hε
  exact ⟨τ, _, _, _, sparsifiesPlain_of (stProgC stStepCount stRootCount stSumLeaves τ k _ (by omega) hτ)⟩

end SplitCount
