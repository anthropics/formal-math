/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachines.Math.Sparsify
public import StepMachines.Math.SparsifyTree
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.List.ProdSigma
public import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! The sparsification lemma of Impagliazzo, Paturi and Zane for 3-CNF: its branching tree, on lists
of clauses: the inclusion-minimal clauses of a list (`redL`) and the nodes of the tree as lists
without repetition (`NodeL`).
-/

namespace Groundwork.Sparsify

open Finset

variable {α : Type*} [DecidableEq α]

/-- The inclusion-minimal clauses of a list. -/
@[expose] public def redL (s : List (Finset α)) : List (Finset α) :=
  s.filter fun C => ∀ D ∈ s, D ⊆ C → D = C

public theorem toFinset_redL (s : List (Finset α)) : (redL s).toFinset = red s.toFinset := by
  ext C
  simp [redL, red]

/-- The list s, without repetition, is a node of the tree of φ (see Node). -/
@[expose] public def NodeL (τ : ℕ) (φ s : List (Finset α)) (p q : ℕ) : Prop :=
  s.Nodup ∧ Node τ φ.toFinset s.toFinset p q

section Main

variable {τ n : ℕ} {lits : List α} {φ s : List (Finset α)} {p q : ℕ}

variable {U : Finset α}

end Main

end Groundwork.Sparsify
