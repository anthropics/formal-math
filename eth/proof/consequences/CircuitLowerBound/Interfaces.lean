/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CircuitLowerBound.Defs

/-! # The circuit lower bound for E^NP (Section 7): the interface statements, as propositions

The main statements that one file needs from another are written here as definitions `St… : Prop`;
the others are written in other files. Nothing is proved and nothing is assumed: this file has no
theorem. One file proves `theorem st… : St…`; a file that needs the statement takes it
as a hypothesis; `proof/consequences/CircuitLowerBound/Main.lean` takes them all as hypotheses, and
another file feeds the proofs in. -/

@[expose] public section

namespace CircuitLowerBound

open ENP Groundwork Turing

/-- Every machine has a table: the formula of the table is satisfiable if and only if the machine
accepts 1^P 0 y for some y within 2^bt steps. -/
def StTab : Prop := ∀ N : TM2ComputableAux Bool Bool, (∀ k, Finite (N.tm.Γ k)) →
  ∃ e : MCode, ∀ L P : ℕ, Fits e L P → (Sat (tabF e L P) ↔ Acc N P (2 ^ bt e L))

/-- Every table has arbitrarily large numbers. -/
def StCode : Prop := ∀ (e : MCode) (a₀ : ℕ), ∃ a, a₀ ≤ a ∧ codeOf a = e

/-- The chains. -/
def StChain : Prop := ∀ a s : ℕ, nu (2 ^ a * (2 * s + 1)) = a ∧ pos (2 ^ a * (2 * s + 1)) = s

/-- The variables of the formula of a table have L bits. -/
def StVars : Prop := ∀ (e : MCode) (L P : ℕ), Fits e L P → ∀ C ∈ tabF e L P, ∀ l ∈ C, l.1 < 2 ^ L

/-- The search finds a satisfying assignment if there is one. -/
def StGreedy : Prop := ∀ (φ : Cnf) (M : ℕ), (∀ C ∈ φ, ∀ l ∈ C, l.1 < M) → Sat φ →
  ∀ C ∈ φ, ∃ l ∈ C, (greedy φ (l.1 + 1)).getD l.1 false = l.2

/-- The algorithm. For every c₀ ONE machine N: (1) if N accepts 1^m 0 y, then `Phi m` is
satisfiable; (2) for every table e there is m₀ such that for all m ≥ m₀ on a chain of e: if a
circuit with at most c₀·(m+1) gates computes a satisfying
assignment of `Phi m`, then N accepts 1^m 0 y for some y within 2^(m/8) steps. N is chosen before e,
and m₀ after e. -/
def StAlg : Prop := ∀ c₀ : ℕ, ∃ N : TM2ComputableAux Bool Bool, (∀ k, Finite (N.tm.Γ k)) ∧
  (∀ m T : ℕ, Acc N m T → Sat (Phi m)) ∧
  ∀ e : MCode, ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → codeOf (nu m) = e → pos m ≤ top (nu m) →
    ∀ C : Circuit, C.length ≤ c₀ * (m + 1) → (∀ D ∈ Phi m, ∃ l ∈ D, eval C (toWord m l.1) = l.2) → Acc N m (2 ^ (m / 8))

/-- The language is in E^NP, second form. -/
def StENP' : Prop := InENP' L0

/-- The language is in E^NP, first form. -/
def StENP : Prop := InENP L0

end CircuitLowerBound
