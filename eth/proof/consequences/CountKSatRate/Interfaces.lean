/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountKSatStatement
public import ThreeSatRateStatement
public import CountKSatRate.Defs
public import PaddedDescent.F.Interfaces

/-! # The interface statements, as propositions

Statements that one file needs from another are written here as definitions `St… : Prop`. Nothing is
proved and nothing is assumed: this file has no
theorem. One file proves `theorem … : St…`; a file that needs the statement takes `(h : St…)` as a
hypothesis.
The width k of the clauses is a variable of every statement in which it occurs. -/

@[expose] public section

namespace CountKSatRate

open Finset Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat PaddedDescent PaddedDescent.F
open WidthK (theta bsum leafC)

/-! ### The tree -/

/-- The sparsification lemma for counting at width k ≥ 1, with a short side list. ψ has variables
below n and nonempty clauses of at most k literals, and τ ≥ k². The tree of
`stepC (theta τ) k` of depth bsum τ k · n has at most Σ_{j ≤ kn/τ} C(bsum τ k · n, j) leaves. The
formula of a leaf has at most (leafC τ k + 2)·n clauses. At a leaf, the
formula that the rule looks at has nonempty clauses of at most k literals on variables below n, and
every variable occurs in at most leafC τ k of them; every clause of the side
list is one of the clauses xᵢ ∨ ¬xᵢ or has exactly one literal, and its variables are below n. The
counts of the leaves add up to the count of ψ. The stack of the walk never
holds more than bsum τ k · n + 1 nodes, each a formula of at most 2^k·|ψ| clauses of at most k
literals and a side list of at most 2n clauses of at most 2 literals. -/
def StTreeK : Prop := ∀ (k τ n : ℕ), 1 ≤ k → k ^ 2 ≤ τ → ∀ ψ : PFml, (∀ C ∈ ψ, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) →
  (leaves (stepC (theta τ) k) (bsum τ k * n) (rootC (List.replicate n (), ψ))).length ≤ ∑ j ∈ range (k * n / τ + 1), (bsum τ k * n).choose j ∧
  (∀ x ∈ leaves (stepC (theta τ) k) (bsum τ k * n) (rootC (List.replicate n (), ψ)),
    stepC (theta τ) k x = none ∧ (leafF x).length ≤ (leafC τ k + 2) * n ∧
      (∀ C ∈ x.1, C ≠ [] ∧ C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧ (∀ v, (Mark.occ x.1 v).length ≤ leafC τ k) ∧
      ∀ C ∈ x.2, (C ∈ taut n ∨ ∃ l, C = [l]) ∧ ∀ l ∈ C, l.1 < n) ∧
  cntN n ψ = ((leaves (stepC (theta τ) k) (bsum τ k * n) (rootC (List.replicate n (), ψ))).map fun x => cntN n (leafF x)).sum ∧
  ∀ i, ((round (stepC (theta τ) k))^[i] ([rootC (List.replicate n (), ψ)], [])).1.length ≤ bsum τ k * n + 1 ∧
    ∀ x ∈ ((round (stepC (theta τ) k))^[i] ([rootC (List.replicate n (), ψ)], [])).1,
      x.1.length ≤ ψ.length * 2 ^ k ∧ x.2.length ≤ 2 * n ∧ (∀ C ∈ x.1, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧ ∀ C ∈ x.2, C.length ≤ 2 ∧ ∀ l ∈ C, l.1 < n

/-! ### The walk -/

/-- The state of the summing walk after i rounds: the stack of the plain walk, and the sum of the
values of the leaves that the plain walk has listed. -/
def StRoundS : Prop := ∀ (σ : Type) (step : σ → Option (σ × σ)) (val : σ → ℕ) (i : ℕ) (st out : List σ),
  (roundS step val)^[i] (st, (out.map val).sum) = (((round step)^[i] (st, out)).1, (((round step)^[i] (st, out)).2.map val).sum)

/-- After at least 2·(number of leaves) − 1 rounds the stack is empty and the number is the sum of
the values of the leaves. -/
def StRoundSEnd : Prop := ∀ (σ : Type) (step : σ → Option (σ × σ)) (val : σ → ℕ) (d : ℕ) (s : σ),
  (∀ x ∈ leaves step d s, step x = none) → ∀ R : ℕ, 2 * (leaves step d s).length - 1 ≤ R →
  (roundS step val)^[R] ([s], 0) = ([], ((leaves step d s).map val).sum)

/-- If the pad has at least 2·(number of leaves) − 1 units and the word of every state of the walk
fits under the pad, then `walkS` returns the sum of the values of the leaves. -/
def StWalkS : Prop := ∀ (k : ℕ) (pad : U) (τ : ℕ) (val : CNode → ℕ) (r : CNode) (d : ℕ),
  (∀ x ∈ leaves (stepC (theta τ) k) d r, stepC (theta τ) k x = none) → 2 * (leaves (stepC (theta τ) k) d r).length ≤ pad.length + 1 →
  (∀ i, len ((roundS (stepC (theta τ) k) val)^[i] ([r], 0)) ≤ pad.length) →
  walkS k pad τ val r = ((leaves (stepC (theta τ) k) d r).map val).sum

/-! ### Correctness -/

/-- The word of a state of the counting walk has length at most `stackLenC k τ n m`. -/
def StStateLen : Prop := ∀ (k τ n m c : ℕ) (st : List CNode), st.length ≤ bsum τ k * n + 1 →
  (∀ x ∈ st, x.1.length ≤ m * 2 ^ k ∧ x.2.length ≤ 2 * n ∧ (∀ C ∈ x.1, C.length ≤ k ∧ ∀ l ∈ C, l.1 < n) ∧ ∀ C ∈ x.2, C.length ≤ 2 ∧ ∀ l ∈ C, l.1 < n) →
  c < 2 ^ (n + 1) → len (st, c) ≤ stackLenC k τ n m

/-- With a pad of at least 2^n units, exhaustive counting is correct. -/
def StBruteC : Prop := ∀ (k n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → SatK.IsKCNF k φ → ∀ w : U, 2 ^ n ≤ w.length → bruteN k (SatK.enc k φ, w) = SatK.numSat φ

/-! ### The polynomial-time certificates -/

/-- The summing walk is polynomial-time in the pad. -/
def StCertWalkS : Prop := ∀ (k : ℕ) (α : Type) [Enc α] (pad : α → U) (τ : α → ℕ) (val : α → CNode → ℕ) (r : α → CNode),
  PolyT pad → PolyT τ → (PolyT fun p : α × CNode => val p.1 p.2) → PolyT r → PolyT fun t => walkS k (pad t) (τ t) (val t) (r t)

/-! ### The machine -/

/-- Let `e` (from bit strings to numbers) and `B` (from a bit string and a list of units to a bit
string) be polynomial-time. There are a Turing machine `N` with finite
alphabets and a number `q` such that on every bit string `x` the machine halts with the output B (x,
the list of 2^(e x) units) within q · (|x| + 2^(e x) + 1)^q steps. -/
def StPaddedW : Prop := ∀ (e : List Bool → ℕ) (B : List Bool × List Unit → List Bool), PolyT e → PolyT B →
  ∃ (N : Turing.TM2ComputableAux Bool Bool) (q : ℕ), (∀ i, Finite (N.tm.Γ i)) ∧
    ∀ x : List Bool, Nonempty (Turing.TM2OutputsInTime N.tm (x.map N.inputAlphabet.invFun)
      (some ((B (x, pad (e x))).map N.outputAlphabet.invFun)) (q * (x.length + 2 ^ e x + 1) ^ q))

end CountKSatRate
