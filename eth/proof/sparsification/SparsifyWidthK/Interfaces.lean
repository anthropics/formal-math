/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsifyWidthK.Defs
public import SparsifyWidthK.DefsProg
public import ToTuring.Poly.Sparsify
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # The interface statements, as propositions

Every statement that one file needs from another is written here as a definition `St… : Prop`.
Nothing is proved and nothing is assumed: this file has no
theorem. One file proves `theorem … : St…`; a file that needs the statement takes `(h : St…)` as a
hypothesis. -/

@[expose] public section

namespace WidthK

open Finset Groundwork Groundwork.Sparsify WidthK.Prog

/-! ### Finite sets: the tree of the rule -/

/-- The root of the tree is a node with both counters 0. -/
def StNodeRoot : Prop := ∀ (α : Type) [DecidableEq α] (θ : ℕ → ℕ) (k τ : ℕ) (φ : Finset (Finset α)), Node θ k τ φ (Sparsify.red φ) 0 0

/-- Both children of a node are nodes: one more step, and τ more units at the heavy child. -/
def StNodeStep : Prop := ∀ (α : Type) [DecidableEq α] (θ : ℕ → ℕ) (k τ : ℕ) (φ F : Finset (Finset α)) (p t j : ℕ) (H : Finset α),
  (∀ i, 1 ≤ θ i) → Node θ k τ φ F p t → Rule θ k F j H →
    Node θ k τ φ (light F H) (p + 1) t ∧ Node θ k τ φ (heavy F j H) (p + 1) (t + τ)

/-- A path has at most (β 0 + … + β (k-1))·n steps, and its heavy steps use at most k·n units, τ
each. U: the at most 2n literals. -/
def StNodeBound : Prop := ∀ (α : Type) [DecidableEq α] (θ β : ℕ → ℕ) (k τ n : ℕ) (φ F : Finset (Finset α)) (U : Finset α) (p t : ℕ),
  Thr τ θ β → U.card ≤ 2 * n → (∀ C ∈ φ, C ⊆ U) → Node θ k τ φ F p t → p ≤ (∑ i ∈ range k, β i) * n ∧ t ≤ k * n

/-- A leaf has at most 2·(θ 0 + … + θ (k-1))·n clauses. -/
def StLeafCard : Prop := ∀ (α : Type) [DecidableEq α] (θ : ℕ → ℕ) (k n : ℕ) (F : Finset (Finset α)) (U : Finset α),
  (∀ i, 1 ≤ θ i) → U.card ≤ 2 * n → (∀ C ∈ F, C ⊆ U ∧ C.Nonempty ∧ C.card ≤ k) → Leaf θ k F → F.card ≤ (2 * ∑ j ∈ range k, θ j) * n

/-- For a heart H of a reduced F, the light child is H together with the clauses of F that do not
contain H. -/
def StLightEq : Prop := ∀ (α : Type) [DecidableEq α] (θ : ℕ → ℕ) (F : Finset (Finset α)) (j : ℕ) (H : Finset α),
  (∀ i, 1 ≤ θ i) → Reduced F → Heart θ F j H → light F H = {H} ∪ F.filter fun C => ¬ H ⊆ C

/-- For a heart H of a reduced F, the heavy child is the petals together with the clauses of F that
contain no petal. -/
def StHeavyEq : Prop := ∀ (α : Type) [DecidableEq α] (θ : ℕ → ℕ) (F : Finset (Finset α)) (j : ℕ) (H : Finset α),
  Reduced F → Heart θ F j H → heavy F j H = petals F j H ∪ F.filter fun C => ∀ D ∈ petals F j H, ¬ D ⊆ C

/-- F is satisfied exactly if one of the children is. -/
def StSatIff : Prop := ∀ (α : Type) [DecidableEq α] (F : Finset (Finset α)) (j : ℕ) (H : Finset α) (v : α → Prop),
  Sat v F ↔ Sat v (light F H) ∨ Sat v (heavy F j H)

/-! ### The thresholds and the number of leaves -/

/-- The thresholds `theta τ` and the bounds `beta τ` have the three properties that the final count
needs. -/
def StThr : Prop := ∀ τ : ℕ, 1 ≤ τ → Thr τ (theta τ) (beta τ)

/-- β 0 + … + β (k-1) is at most `bsum τ k`. -/
def StBetaSum : Prop := ∀ τ k : ℕ, ∑ i ∈ range k, beta τ i ≤ bsum τ k

/-- The bound on the number of leaves, Σ_{j ≤ kn/τ} C(bsum τ k · n, j), is at most 2^{εn} if
(k/τ)·log₂(e·τ·bsum τ k) ≤ ε. -/
def StLeafCount : Prop := ∀ (k τ : ℕ) (ε : ℝ), 1 ≤ τ → ((k : ℝ) / τ) * Real.logb 2 (Real.exp 1 * τ * bsum τ k) ≤ ε →
  ∀ n : ℕ, ((∑ j ∈ range (k * n / τ + 1), (bsum τ k * n).choose j : ℕ) : ℝ) ≤ (2 : ℝ) ^ (ε * n)

/-- For every ε > 0 some τ, as large as we like, has (k/τ)·log₂(e·τ·bsum τ k) ≤ ε. -/
def StExistsTau : Prop := ∀ (k τ₀ : ℕ) (ε : ℝ), 0 < ε →
  ∃ τ : ℕ, τ₀ ≤ τ ∧ 4 ≤ τ ∧ ((k : ℝ) / τ) * Real.logb 2 (Real.exp 1 * τ * bsum τ k) ≤ ε

/-! ### The program -/

/-- What the walk of the tree needs to know about the rule on finite sets. `Node F₀ F p t`: F is a
node of the tree of F₀ after p steps and t units, of which a
heavy step uses q. `Ok F₀` is a condition on the formula at the start. D and T bound p and t, and
`leafB` bounds the number of clauses of a leaf. -/
structure Iface (θ : ℕ → ℕ) (k D T q leafB : ℕ) (Ok : Finset (Finset PLit) → Prop)
    (Node : Finset (Finset PLit) → Finset (Finset PLit) → ℕ → ℕ → Prop) : Prop where
  root : ∀ F₀, Ok F₀ → Node F₀ (red F₀) 0 0
  step : ∀ F₀ F p t j H, Node F₀ F p t → Rule θ k F j H → Node F₀ (light F H) (p + 1) t ∧ Node F₀ (heavy F j H) (p + 1) (t + q)
  bound : ∀ F₀ F p t, Node F₀ F p t → p ≤ D ∧ t ≤ T
  clause : ∀ F₀ F p t, Node F₀ F p t → ∀ C ∈ F, ∃ C₀ ∈ F₀, C ⊆ C₀
  leaf : ∀ F₀ F p t, Node F₀ F p t → Leaf θ k F → F.card ≤ leafB
  sat : ∀ F₀ F p t j H (v : PLit → Prop), Node F₀ F p t → Rule θ k F j H → (Sat v F ↔ Sat v (light F H) ∨ Sat v (heavy F j H))
  light_eq : ∀ F₀ F p t j H, Node F₀ F p t → Rule θ k F j H → light F H = {H} ∪ F.filter fun C => ¬ H ⊆ C
  heavy_eq : ∀ F₀ F p t j H, Node F₀ F p t → Rule θ k F j H →
    heavy F j H = petals F j H ∪ F.filter fun C => ∀ D ∈ petals F j H, ¬ D ⊆ C

/-- The functions on lists carry out the rule on finite sets. On a formula in normal form, `pickK`
returns a heart and its petals as the rule demands, or `none`
at a leaf; `rootP` returns a formula in normal form whose set of clauses is the set of the
inclusion-minimal clauses. -/
structure Refines (θ : ℕ → ℕ) (k : ℕ) : Prop where
  some : ∀ s H P, NF s → pickK θ k s = some (H, P) →
    ∃ j, Rule θ k (toFin s) j H.toFinset ∧ toFin P = petals (toFin s) j H.toFinset ∧ NF P ∧ H.Nodup
  none : ∀ s, NF s → pickK θ k s = none → Leaf θ k (toFin s)
  nf_root : ∀ ψ, NF (rootP ψ)
  toFin_root : ∀ ψ, toFin (rootP ψ) = red (toFin ψ)

/-- `Refines` holds whenever all thresholds are at least 1. -/
def StRefines : Prop := ∀ (θ : ℕ → ℕ) (k : ℕ), (∀ i, 1 ≤ θ i) → Refines θ k

/-- The sparsification lemma for width k, for the functions `stepK` and `rootP` with the thresholds
`theta τ`. ψ has variables below n and nonempty clauses of
at most k literals. There are at most Σ_{j ≤ kn/τ} C(bsum τ k · n, j) leaves, each with at most
leafC τ k · n clauses; ψ is satisfied exactly if some leaf is;
the stack of the walk never holds more than bsum τ k · n + 1 formulas, each with at most 2^k times
as many clauses as ψ. -/
def StProg : Prop := ∀ (τ k n : ℕ), 1 ≤ τ → ∀ ψ : PFml, (∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) →
  (leaves (stepK (theta τ) k) (bsum τ k * n) (rootP ψ)).length ≤ ∑ j ∈ range (k * n / τ + 1), (bsum τ k * n).choose j ∧
  (∀ x ∈ leaves (stepK (theta τ) k) (bsum τ k * n) (rootP ψ),
    stepK (theta τ) k x = none ∧ x.length ≤ leafC τ k * n ∧ ∀ C ∈ x, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧
  (∀ v : PLit → Prop, (∀ C ∈ ψ, ∃ a ∈ C, v a) ↔ ∃ x ∈ leaves (stepK (theta τ) k) (bsum τ k * n) (rootP ψ), ∀ C ∈ x, ∃ a ∈ C, v a) ∧
  ∀ i, ((round (stepK (theta τ) k))^[i] ([rootP ψ], [])).1.length ≤ bsum τ k * n + 1 ∧
    ∀ x ∈ ((round (stepK (theta τ) k))^[i] ([rootP ψ], [])).1, x.length ≤ ψ.length * 2 ^ k ∧
      ∀ C ∈ x, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n

/-- One step of the tree is computed in polynomial time. -/
def StCertStep : Prop := ∀ (θ : ℕ → ℕ) (k : ℕ), PolyT (stepK θ k)

end WidthK
