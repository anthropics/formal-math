/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachines.Math.SparsifyStep
public import StepMachines.Math.SparsifyCount
public import ThreeSatStatement
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.BigOperators

/-! Two tools for the branching tree of the sparsification lemma of Impagliazzo, Paturi and Zane,
with the formulas written as plain lists of lists of literals.
`leaves_sim`: a map that carries one step function to another on the states with an invariant
carries the leaves of the one tree to the leaves of the other.
`redLL` keeps the inclusion-minimal clauses of a list, and `map_redLL` says that it agrees with
`redL` on finsets. -/

namespace Groundwork.Sparsify

open Finset

section Sim

variable {σ σ' : Type*} {step' : σ' → Option (σ' × σ')} {step : σ → Option (σ × σ)} {f : σ' → σ} {I : σ' → Prop}

/-- If f carries step' to step on the states with I, it carries leaves to leaves. -/
public theorem leaves_sim (hsim : ∀ s, I s → (step' s).map (Prod.map f f) = step (f s))
    (hinv : ∀ s l h, I s → step' s = some (l, h) → I l ∧ I h) (k : ℕ) (s : σ') (hs : I s) :
    (leaves step' k s).map f = leaves step k (f s) ∧ ∀ x ∈ leaves step' k s, I x := by
  induction k generalizing s with
  | zero => simp [leaves, hs]
  | succ k ih =>
    have h1 := hsim s hs
    cases h0 : step' s with
    | none =>
      rw [h0] at h1
      simp [leaves, h0, ← h1, hs]
    | some lh =>
      obtain ⟨l, h⟩ := lh
      rw [h0] at h1
      obtain ⟨hl, hh⟩ := hinv s l h hs h0
      have e : leaves step (k + 1) (f s) = leaves step k (f l) ++ leaves step k (f h) := by
        simp [leaves, ← h1]
      have e' : leaves step' (k + 1) s = leaves step' k l ++ leaves step' k h := by simp [leaves, h0]
      rw [e, e', List.map_append, (ih l hl).1, (ih h hh).1]
      refine ⟨rfl, fun x hx => ?_⟩
      rcases List.mem_append.1 hx with hx | hx
      exacts [(ih l hl).2 x hx, (ih h hh).2 x hx]

end Sim

variable {α : Type*} [DecidableEq α]

/-- The inclusion-minimal clauses of a list. -/
@[expose] public def redLL (s : List (List α)) : List (List α) :=
  s.filter fun C => ∀ D ∈ s, (∀ a ∈ D, a ∈ C) → ∀ a ∈ C, a ∈ D

public theorem map_redLL (s : List (List α)) : (redLL s).map List.toFinset = redL (s.map List.toFinset) := by
  rw [redLL, redL, List.filter_map]
  congr 1
  apply List.filter_congr
  intro C _
  simp only [Function.comp, List.forall_mem_map, decide_eq_decide]
  refine forall₂_congr fun D _ => ?_
  constructor
  · intro h hDC
    exact Finset.Subset.antisymm hDC fun a ha =>
      List.mem_toFinset.2 (h (fun a ha => List.mem_toFinset.1 (hDC (List.mem_toFinset.2 ha))) a (List.mem_toFinset.1 ha))
  · intro h hDC a ha
    have := h fun a ha => List.mem_toFinset.2 (hDC a (List.mem_toFinset.1 ha))
    exact List.mem_toFinset.1 (this ▸ List.mem_toFinset.2 ha)

section Main

variable [Fintype α] {τ n : ℕ} {lits : List α} {φ : List (List α)}

end Main

end Groundwork.Sparsify
