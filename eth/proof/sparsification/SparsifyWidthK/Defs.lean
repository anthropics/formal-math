/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepMachines.Math.Sparsify

/-! # The sparsification of a k-CNF on finite sets: definitions

Literals are elements of any type α; a clause is a `Finset α`, a formula a `Finset (Finset α)`.
`Sat`, `Reduced`, `red` and `over` are those of
`StepMachines/Math/Sparsify.lean`: `over F j H` is the set of the clauses of F of size j that
contain H.
The branching rule is that of Impagliazzo, Paturi and Zane. A heart is a nonempty set H that lies in
at least θ (j - |H|) clauses of size j > |H|; the
petals are these clauses without H. The rule takes the smallest such j and, for it, a heart of the
largest size. The light child adds H as a clause, the heavy
child adds all petals; both keep only the inclusion-minimal clauses.
This file has definitions only; the proofs are in `SparsifyWidthK/Step.lean`,
`SparsifyWidthK/SetAlg.lean` and `SparsifyWidthK/Thresholds.lean`.
(`Mathlib.Tactic` makes the word `over` a keyword, so the files of this folder write
`Sparsify.over`.) -/

@[expose] public section

namespace WidthK

open Finset Groundwork Groundwork.Sparsify

variable {α : Type*} [DecidableEq α]

/-! ### The rule -/

/-- The clauses of size j over H, without H. -/
def petals (F : Finset (Finset α)) (j : ℕ) (H : Finset α) : Finset (Finset α) := (Sparsify.over F j H).image (· \ H)

/-- The light child: H becomes a clause. -/
def light (F : Finset (Finset α)) (H : Finset α) : Finset (Finset α) := Sparsify.red (F ∪ {H})

/-- The heavy child: the petals become clauses. -/
def heavy (F : Finset (Finset α)) (j : ℕ) (H : Finset α) : Finset (Finset α) := Sparsify.red (F ∪ petals F j H)

/-- H is a heart for the clauses of size j: nonempty, smaller than j, and in at least θ (j - |H|) of
them. -/
def Heart (θ : ℕ → ℕ) (F : Finset (Finset α)) (j : ℕ) (H : Finset α) : Prop :=
  H.Nonempty ∧ H.card < j ∧ θ (j - H.card) ≤ (Sparsify.over F j H).card

/-- The rule applies at F with clause size j and heart H: j is the smallest size that has a heart, H
a largest heart for j. -/
structure Rule (θ : ℕ → ℕ) (k : ℕ) (F : Finset (Finset α)) (j : ℕ) (H : Finset α) : Prop where
  le : j ≤ k
  heart : Heart θ F j H
  minj : ∀ j' < j, ∀ H', ¬ Heart θ F j' H'
  maxH : ∀ H', H.card < H'.card → ¬ Heart θ F j H'

/-- A leaf: no size up to k has a heart. -/
def Leaf (θ : ℕ → ℕ) (k : ℕ) (F : Finset (Finset α)) : Prop := ∀ j ≤ k, ∀ H, ¬ Heart θ F j H

/-! ### One step and the accounts along a path -/

/-- The clauses of size i. -/
def lay (N : Finset (Finset α)) (i : ℕ) : Finset (Finset α) := N.filter fun C => C.card = i

/-- What one step adds to F: proper subsets of clauses of F, all of one size r ≥ 1, such that every
literal lies in at most d r sets that are
clauses of F of size r or are added. -/
structure AddK (d : ℕ → ℕ) (F A : Finset (Finset α)) (r : ℕ) : Prop where
  ssub : ∀ D ∈ A, ∃ C ∈ F, D ⊂ C
  size : ∀ D ∈ A, D.card = r
  pos : 0 < r
  deg : ∀ y, (Sparsify.over F r {y}).card + (A.filter fun D => y ∈ D).card ≤ d r

/-- The invariant along a path. N: the added clauses that are still present; a i: how many clauses
of size i were added so far. Every literal lies in
at most d i clauses of N of size i, and a i is at most the number of clauses of size i in N plus d i
for every smaller clause added so far. -/
structure InvK (d : ℕ → ℕ) (F N : Finset (Finset α)) (a : ℕ → ℕ) : Prop where
  red : Reduced F
  sub : N ⊆ F
  deg : ∀ i y, ((lay N i).filter fun C => y ∈ C).card ≤ d i
  acc : ∀ i, a i ≤ (lay N i).card + d i * ∑ i' ∈ range i, a i'

/-- N after a step that adds A. -/
def nextN (N A : Finset (Finset α)) : Finset (Finset α) := A ∪ N.filter fun C => ∀ D ∈ A, ¬ D ⊆ C

/-- The counts after a step that adds c clauses of size r. -/
def nextA (a : ℕ → ℕ) (r c : ℕ) : ℕ → ℕ := fun i => a i + if i = r then c else 0

/-- The degree bound that belongs to the thresholds θ: 2·θ(i-1) at size i ≥ 1. -/
def dg (θ : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => 2 * θ i

/-- What holds of a node F of the tree of φ after p steps, each heavy step adding τ to t. h r counts
the heavy steps with petals of size r. -/
def Node (θ : ℕ → ℕ) (k τ : ℕ) (φ F : Finset (Finset α)) (p t : ℕ) : Prop :=
  (∀ C ∈ F, ∃ C' ∈ φ, C ⊆ C' ∧ (C'.Nonempty → C.Nonempty)) ∧
    ∃ (N : Finset (Finset α)) (a h : ℕ → ℕ), InvK (dg θ) F N a ∧ a 0 = 0 ∧ (∀ r, h r * θ r ≤ a r) ∧
      p ≤ ∑ i ∈ range k, a i ∧ t ≤ τ * ∑ r ∈ range k, h r

/-! ### The thresholds -/

/-- What the final count needs of thresholds θ and bounds β: at most β i · n clauses of size i are
added along a path, n the number of variables. -/
structure Thr (τ : ℕ) (θ β : ℕ → ℕ) : Prop where
  pos : ∀ i, 0 < θ i
  step : ∀ i, 2 * θ i * (2 + ∑ j ∈ range (i + 1), β j) ≤ β (i + 1)
  mul : ∀ r, τ * β r ≤ θ r

/-- (θ i, 2 + β 1 + … + β i) by one recursion. -/
def thrPair (τ : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, 2)
  | i + 1 => (2 * τ * (thrPair τ i).1 * (thrPair τ i).2, (thrPair τ i).2 * (1 + 2 * (thrPair τ i).1))

/-- The thresholds: θ 0 = 1 and θ (i+1) = τ · β (i+1). -/
def theta (τ i : ℕ) : ℕ := (thrPair τ i).1

/-- 2 + β 1 + … + β i. A path of the tree has at most bsum τ k · n steps. -/
def bsum (τ i : ℕ) : ℕ := (thrPair τ i).2

/-- β (i+1) = 2 · θ i · (2 + β 1 + … + β i): at most β i · n clauses of size i are added along a
path. -/
def beta (τ : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => 2 * theta τ i * bsum τ i

/-- A leaf has at most leafC τ k · n clauses. -/
def leafC (τ k : ℕ) : ℕ := 2 * ∑ j ∈ range k, theta τ j

end WidthK
