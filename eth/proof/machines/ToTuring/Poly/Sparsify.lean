/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachines.Math.SparsifyProg
public import ToTuring.Lib.List3

/-! The plain functions of the walk of the sparsification tree, defined in
`StepMachines.Math.SparsifyProg`, are polynomial-time (`PolyT`). Every certificate is stated for
arguments that depend on a
context x, the form in which the tactic `fun_prop` can use it. -/

@[expose] public section

namespace Groundwork.Sparsify

variable {α : Type} [Enc α]

@[fun_prop] theorem polyT_subP {D C : α → PCl} (hD : PolyT D) (hC : PolyT C) : PolyT fun x => subP (D x) (C x) := by
  unfold subP; fun_prop

@[fun_prop] theorem polyT_overP {s : α → PFml} {i : α → ℕ} {S : α → PCl} (hs : PolyT s) (hi : PolyT i) (hS : PolyT S) :
    PolyT fun x => overP (s x) (i x) (S x) := by
  unfold overP; fun_prop

@[fun_prop] theorem polyT_addP {A s : α → PFml} (hA : PolyT A) (hs : PolyT s) : PolyT fun x => addP (A x) (s x) := by
  unfold addP; fun_prop

@[fun_prop] theorem polyT_redP {s : α → PFml} (hs : PolyT s) : PolyT fun x => redP (s x) := by
  unfold redP; fun_prop

@[fun_prop] theorem polyT_minusP {H C : α → PCl} (hH : PolyT H) (hC : PolyT C) : PolyT fun x => minusP (H x) (C x) := by
  unfold minusP; fun_prop

@[fun_prop] theorem polyT_litsOf {s : α → PFml} (hs : PolyT s) : PolyT fun x => litsOf (s x) := by
  unfold litsOf; fun_prop

@[fun_prop] theorem polyT_canonP {ls C : α → PCl} (hl : PolyT ls) (hC : PolyT C) : PolyT fun x => canonP (ls x) (C x) := by
  unfold canonP; fun_prop

/-- The root of the sparsification tree is computed in polynomial time. -/
@[fun_prop] theorem polyT_rootP {φ : α → PFml} (hφ : PolyT φ) : PolyT fun x => rootP (φ x) := by
  unfold rootP; fun_prop

/-- `greedyP k`, which picks at most k clauses of l that share no literal with `used` or with one
another, is
polynomial-time for every fixed k: the number of rounds is a constant of the machine. The induction
on k needs all
contexts α at once. -/
theorem polyT_greedyP' (k : ℕ) : ∀ {α : Type} [Enc α] {used : α → PCl} {l : α → PFml}, PolyT used → PolyT l →
    PolyT fun x => greedyP k (used x) (l x) := by
  induction k with
  | zero => intro α _ used l _ _; unfold greedyP; fun_prop
  | succ k ih =>
    intro α _ used l hu hl
    have h1 : PolyT fun p : α × PCl => greedyP k (used p.1 ++ p.2) (l p.1) := ih (by fun_prop) (by fun_prop)
    have h : PolyT fun x => ((l x).find? fun Q => Q.all fun a => !((used x).elem a)).elim []
        fun Q => Q :: greedyP k (used x ++ Q) (l x) := by fun_prop
    refine h.congr fun x => ?_
    rw [greedyP]
    cases (l x).find? fun Q => Q.all fun a => !((used x).elem a) <;> rfl

@[fun_prop] theorem polyT_greedyP (k : ℕ) {used : α → PCl} {l : α → PFml} (hu : PolyT used) (hl : PolyT l) :
    PolyT fun x => greedyP k (used x) (l x) := polyT_greedyP' k hu hl

/-- `pickP` with its case distinctions written by `Option.elim`. -/
theorem pickP_eq (τ : ℕ) (s : PFml) : pickP τ s =
    ((litsOf s).find? fun a => decide (τ ≤ (overP s 2 [a]).length)).elim
      (((List.product (litsOf s) (litsOf s)).find? fun ab =>
          !(ab.1 == ab.2) && decide (τ ≤ (overP s 3 [ab.1, ab.2]).length)).elim
        (((litsOf s).find? fun a => decide (2 * τ ^ 3 ≤ (overP s 3 [a]).length)).elim none
          fun a => some ([a], greedyP (τ ^ 2) [] ((overP s 3 [a]).map (minusP [a]))))
        fun ab => some ([ab.1, ab.2], ((overP s 3 [ab.1, ab.2]).take τ).map (minusP [ab.1, ab.2])))
      fun a => some ([a], ((overP s 2 [a]).take τ).map (minusP [a])) := by
  unfold pickP
  split
  · next a h => rw [h]; rfl
  · next h =>
    rw [h]
    split
    · next ab h' => rw [h']; rfl
    · next h' =>
      rw [h']
      split
      · next a h'' => rw [h'']; rfl
      · next h'' => rw [h'']; rfl

/-- The choice of the branching rule at a node is polynomial-time. -/
@[fun_prop] theorem polyT_pickP (τ : ℕ) {s : α → PFml} (hs : PolyT s) : PolyT fun x => pickP τ (s x) := by
  simp only [pickP_eq]; fun_prop

/-- The two children of a node of the sparsification tree are computed in polynomial time. -/
@[fun_prop] theorem polyT_stepP (τ : ℕ) {s : α → PFml} (hs : PolyT s) : PolyT fun x => stepP τ (s x) := by
  unfold stepP; fun_prop

end Groundwork.Sparsify
