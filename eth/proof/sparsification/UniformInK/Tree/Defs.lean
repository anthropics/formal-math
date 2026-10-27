/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import UniformInK.Spars.Defs
public import ClauseBound.TopN.Defs

/-! # The counting tree for the geometric thresholds: definitions and interface statements

The counting tree of `stepC (thetaU τ) k` for width k with the thresholds `thetaU τ`: the bound
`stackLenCU` on the length of the word of a state, and the statements `StTreeU` and `StStateLenU`.
This file has definitions only. The statements `St…` are propositions. -/

@[expose] public section

namespace UniformInK

open Finset Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat PaddedDescent PaddedDescent.F CountKSatRate
open PaddedDescent.F.Mark (occ)

/-- An upper bound for the length of the word of a state (a stack of nodes and a number): at most
bsumU τ k · n + 1 nodes, each a formula of at most 2^k·m clauses of at most k literals and a side
list of at most 2n clauses of at most 2 literals, all on variables below n; and a number below
2^(n+1). -/
def stackLenCU (k τ n m : ℕ) : ℕ :=
  (bsumU τ k * n + 1) * (2 ^ k * m * (k * (3 * n + 5) + 10) + 2 * n * (2 * (3 * n + 5) + 10) + 8) + 3 * n + 16

/-- The sparsification lemma for counting at width k ≥ 1, for τ ≥ k² and τ ≥ 8k, for the tree of
`stepC (thetaU τ) k` of depth bsumU τ k · n: a bound on the number of leaves, the shape of the
leaves,
the count of ψ as the sum of the counts of the leaves, and bounds on the stacks of the rounds. -/
def StTreeU : Prop := ∀ (k τ n : ℕ), 1 ≤ k → k ^ 2 ≤ τ → 8 * k ≤ τ → ∀ ψ : PFml, (∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) →
  (leaves (stepC (thetaU τ) k) (bsumU τ k * n) (rootC (List.replicate n (), ψ))).length ≤ ∑ j ∈ range (k * n / τ + 1), (bsumU τ k * n).choose j ∧
  (∀ x ∈ leaves (stepC (thetaU τ) k) (bsumU τ k * n) (rootC (List.replicate n (), ψ)),
    stepC (thetaU τ) k x = none ∧ (leafF x).length ≤ (leafCU τ k + 2) * n ∧
      (∀ C ∈ x.1, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧ (∀ v, (occ x.1 v).length ≤ leafCU τ k) ∧
      ∀ C ∈ x.2, (C ∈ taut n ∨ ∃ l, C = [l]) ∧ ∀ l ∈ C, l.1 < n) ∧
  cntN n ψ = ((leaves (stepC (thetaU τ) k) (bsumU τ k * n) (rootC (List.replicate n (), ψ))).map fun x => cntN n (leafF x)).sum ∧
  ∀ i, ((round (stepC (thetaU τ) k))^[i] ([rootC (List.replicate n (), ψ)], [])).1.length ≤ bsumU τ k * n + 1 ∧
    ∀ x ∈ ((round (stepC (thetaU τ) k))^[i] ([rootC (List.replicate n (), ψ)], [])).1,
      x.1.length ≤ ψ.length * 2 ^ k ∧ x.2.length ≤ 2 * n ∧ (∀ C ∈ x.1, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧ ∀ C ∈ x.2, C.length ≤ 2 ∧ ∀ l ∈ C, l.1 < n

/-- The word of a state, a stack of at most bsumU τ k · n + 1 nodes of bounded size and a number
below 2^(n+1), has length at most `stackLenCU k τ n m`. -/
def StStateLenU : Prop := ∀ (k τ n m c : ℕ) (st : List CNode), st.length ≤ bsumU τ k * n + 1 →
  (∀ x ∈ st, x.1.length ≤ m * 2 ^ k ∧ x.2.length ≤ 2 * n ∧ (∀ C ∈ x.1, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧ ∀ C ∈ x.2, C.length ≤ 2 ∧ ∀ l ∈ C, l.1 < n) →
  c < 2 ^ (n + 1) → len (st, c) ≤ stackLenCU k τ n m

end UniformInK
