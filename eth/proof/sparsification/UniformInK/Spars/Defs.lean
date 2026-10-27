/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsifyWidthK.Interfaces
public import SparsifyWidthK.ProgMain

/-! # The sparsification with geometric thresholds: definitions and interface statements

The rule, the hearts, the petals, the two children and the leaves are those of
proof/sparsification/SparsifyWidthK/Defs.lean. What differs is the invariant along a path of the
tree and, with it, the thresholds.
There every literal lies in at most 2·θ(i−1) added clauses of size i, and an added clause is charged
with the removal of that many clauses of size i, whatever its own size; this forces thresholds
that grow doubly exponentially in k. Here every nonempty SET Y of literals lies in at most
2·θ(i−|Y|) added clauses of size i, so that an added clause of size i' removes at most 2·θ(i−i')
clauses
of size i. This is in substance the count in the Sparsification Lemma of Calabro, Impagliazzo and
Paturi [CIP06]. It allows θ 0 = 1 and θ i = 4·τ^(2i−1) for i ≥ 1, which do not depend on k, as soon
as 1 ≤ k and 8k ≤ τ.
This file has definitions only. The statements `St…` are propositions; one file proves each of them. -/

@[expose] public section

namespace UniformInK

open Finset Groundwork Groundwork.Sparsify WidthK WidthK.Prog

variable {α : Type*} [DecidableEq α]

/-! ### One step and the accounts along a path -/

/-- What one step adds to F: proper subsets of clauses of F, all of one size r ≥ 1, such that every
nonempty set Y of at most r literals lies in at most 2·θ(r−|Y|) sets that are clauses of F of
size r or are added. -/
structure AddU (θ : ℕ → ℕ) (F A : Finset (Finset α)) (r : ℕ) : Prop where
  ssub : ∀ D ∈ A, ∃ C ∈ F, D ⊂ C
  size : ∀ D ∈ A, D.card = r
  pos : 0 < r
  deg : ∀ Y : Finset α, Y.Nonempty → Y.card ≤ r → (Sparsify.over F r Y).card + (A.filter fun D => Y ⊆ D).card ≤ 2 * θ (r - Y.card)

/-- The invariant along a path. N: the added clauses that are still present; a i: how many clauses
of size i were added so far. Every nonempty set Y of at most i literals lies in at most
2·θ(i−|Y|) clauses of N of size i, and a i is at most the number of clauses of size i in N plus
2·θ(i−i') for every clause of a smaller size i' added so far. -/
structure InvU (θ : ℕ → ℕ) (F N : Finset (Finset α)) (a : ℕ → ℕ) : Prop where
  red : Reduced F
  sub : N ⊆ F
  deg : ∀ i (Y : Finset α), Y.Nonempty → Y.card ≤ i → ((lay N i).filter fun C => Y ⊆ C).card ≤ 2 * θ (i - Y.card)
  acc : ∀ i, a i ≤ (lay N i).card + ∑ i' ∈ range i, 2 * θ (i - i') * a i'

/-- What holds of a node F of the tree of φ after p steps, each heavy step adding τ to t. h r counts
the heavy steps with petals of size r. -/
def NodeU (θ : ℕ → ℕ) (k τ : ℕ) (φ F : Finset (Finset α)) (p t : ℕ) : Prop :=
  (∀ C ∈ F, ∃ C' ∈ φ, C ⊆ C' ∧ (C'.Nonempty → C.Nonempty)) ∧
    ∃ (N : Finset (Finset α)) (a h : ℕ → ℕ), InvU θ F N a ∧ a 0 = 0 ∧ (∀ r, h r * θ r ≤ a r) ∧
      p ≤ ∑ i ∈ range k, a i ∧ t ≤ τ * ∑ r ∈ range k, h r

/-! ### The thresholds -/

/-- What the final count needs of thresholds θ and bounds β for width k: at most β i · n clauses of
size i < k are added along a path, n the number of variables. -/
structure ThrU (k τ : ℕ) (θ β : ℕ → ℕ) : Prop where
  pos : ∀ i, 0 < θ i
  step : ∀ i, 0 < i → i < k → 4 * θ (i - 1) + ∑ i' ∈ range i, 2 * θ (i - i') * β i' ≤ β i
  mul : ∀ r, τ * β r ≤ θ r

/-- The thresholds: θ 0 = 1 and θ i = 4·τ^(2i−1). -/
def thetaU (τ : ℕ) : ℕ → ℕ
  | 0 => 1
  | i + 1 => 4 * τ ^ (2 * i + 1)

/-- β 0 = 0 and β i = 4·τ^(2i−2): at most β i · n clauses of size i are added along a path. -/
def betaSU (τ : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => 4 * τ ^ (2 * i)

/-- For 1 ≤ k and 8k ≤ τ, a path of the tree on n variables has at most bsumU τ k · n steps. -/
def bsumU (τ k : ℕ) : ℕ := τ ^ (2 * k)

/-- A leaf on n variables has at most leafCU τ k · n clauses. -/
def leafCU (τ k : ℕ) : ℕ := 2 * ∑ j ∈ range k, thetaU τ j

/-! ### The interface statements -/

/-- The root of the tree is a node with both counters 0. -/
def StNodeRootU : Prop := ∀ (α : Type) [DecidableEq α] (θ : ℕ → ℕ) (k τ : ℕ) (φ : Finset (Finset α)), NodeU θ k τ φ (Sparsify.red φ) 0 0

/-- Both children of a node are nodes: one more step, and τ more units at the heavy child. -/
def StNodeStepU : Prop := ∀ (α : Type) [DecidableEq α] (θ : ℕ → ℕ) (k τ : ℕ) (φ F : Finset (Finset α)) (p t j : ℕ) (H : Finset α),
  (∀ i, 1 ≤ θ i) → NodeU θ k τ φ F p t → Rule θ k F j H →
    NodeU θ k τ φ (light F H) (p + 1) t ∧ NodeU θ k τ φ (heavy F j H) (p + 1) (t + τ)

/-- A path has at most (β 0 + … + β (k-1))·n steps, and its heavy steps use at most k·n units, τ
each. U: the at most 2n literals. -/
def StNodeBoundU : Prop := ∀ (α : Type) [DecidableEq α] (θ β : ℕ → ℕ) (k τ n : ℕ) (φ F : Finset (Finset α)) (U : Finset α) (p t : ℕ),
  ThrU k τ θ β → U.card ≤ 2 * n → (∀ C ∈ φ, C ⊆ U) → NodeU θ k τ φ F p t → p ≤ (∑ i ∈ range k, β i) * n ∧ t ≤ k * n

/-- The thresholds `thetaU τ` and the bounds `betaSU τ` have the three properties for width k, if 1
≤ k and 8k ≤ τ. -/
def StThrU : Prop := ∀ k τ : ℕ, 1 ≤ k → 8 * k ≤ τ → ThrU k τ (thetaU τ) (betaSU τ)

/-- β 0 + … + β (k-1) is at most `bsumU τ k`, if 2 ≤ τ. -/
def StBetaSumU : Prop := ∀ τ k : ℕ, 2 ≤ τ → ∑ i ∈ range k, betaSU τ i ≤ bsumU τ k

/-- All that the walk of the tree needs to know about the rule on finite sets, for the thresholds
`thetaU τ`, if 1 ≤ k and 8k ≤ τ. -/
def StIfaceU : Prop := ∀ τ k n : ℕ, 1 ≤ k → 8 * k ≤ τ →
  Iface (thetaU τ) k (bsumU τ k * n) (k * n) τ (leafCU τ k * n) (ProgMain.Ok k n) (fun F₀ F p t => ProgMain.Ok k n F₀ ∧ NodeU (thetaU τ) k τ F₀ F p t)

end UniformInK
