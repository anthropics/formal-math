/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClausesOccurStatement

/-! # The bound in the number n of variables, for fixed k

Definitions and statements only (no theorem, no proof). Imports `ClausesOccurStatement.lean` (and
through it `MainTheoremFormsStatement.lean`, `AppRunningTimeStatement.lean`).

## The sentences of the paper that are stated here

* Theorem A (c), second sentence: «For fixed k and n ≥ 4 variables the time is 2^{O(n log log n/(log
  n)^{α'})}, provided that a number between 0.85ρ^ℓ and ρ^ℓ can be computed from ℓ in time
  polynomial in K_ℓ, as is the case for ρ = 11/12 and for ρ = 1/√2.»
  This is `CountsFromPieces`, with `Proviso` and `ProvisoHolds`.
* Theorem A as a whole, with both sentences of (c) with the printed hypotheses and quantifiers, in
  steps of a Turing machine: `RunningTimesFromPieces`.

## How to read it

* «One deterministic algorithm … For fixed k … the time is»: ONE machine M with finite alphabets,
  fixed before k; for every k ≥ 1 a constant C, which may depend on k. Both may depend on ρ, c, x₀.
* φ is a k-CNF on the n variables x₀ … xₙ₋₁ (`SatK.IsKCNF k φ`). This n is that of Theorem D (a),
  from which the sentence is proved: the number of all variables, not of those that occur as in the
  first sentence of (c); variables need not occur, and any number of clauses is allowed. The count
  is that of all 2ⁿ assignments, in n + 1 bits (`MainTheoremForms.CountsWithin`); the input is
  `SatM.enc k φ` (1ᵏ 0, 1ⁿ 0, k slots per clause).
* `MainTheoremForms.lg` is the paper's log = log₂, without any shift. The bound has the printed form
  2^{C·…}, rounded down. For n ≥ 4 we have log n ≥ 2 and log log n ≥ 1.
* The numbers K_ℓ of the proviso are those of the display that defines K_ℓ in Theorem A, for the x₀
  of Theorem A (`Levels.Gen.K x₀ ℓ`). «In time polynomial in K_ℓ»: the function gets ℓ and K_ℓ in
  unary and is polynomial-time (`Groundwork.PolyT`); it returns the numerator and the denominator of
  the number.

## Where these statements differ from the printed sentence

* Steps of a multi-stack Turing machine in place of operations of a word RAM; the width k is
  declared in the input, in unary; lists in place of sets: as for the Main Theorem.
* The machine is not that of the first sentence of (c) (`ClausesOccur.CountsFromPieces`): as in the
  printed proof, it is the algorithm of Theorem D (a) with a fall-back.
* `AppRunningTime.ThmRunningTime.c_n` is stronger in that it has no proviso, and weaker in that its
  machine is chosen after k. Its bound (shifted logarithms, a factor C in front) and its code
  (`SatK.enc k φ`, without 1ᵏ 0) convert to those of this file for fixed k. -/

@[expose] public section

namespace FixedWidth

open Turing MainTheoremForms Groundwork PaddedDescent.F
open Sat3 (CNF)

/-- The exponent in the number n of variables, as printed in Theorem A (c): n·log log n/(log n)^α. -/
noncomputable def expVariables (α : ℝ) (n : ℕ) : ℝ := (n : ℝ) * lg (lg n) / lg n ^ α

/-- The time 2^{C·n·log log n/(log n)^α}, rounded down. -/
noncomputable def timeVariables (α : ℝ) (C n : ℕ) : ℕ := ⌊(2 : ℝ) ^ ((C : ℝ) * expVariables α n)⌋₊

/-- For the width k, the machine M and the constant C: for every n ≥ 4 and every k-CNF φ on n
variables, M computes the number of satisfying assignments within 2^{C·n·log log n/(log n)^α} steps. -/
def CountsFor (α : ℝ) (k : ℕ) (M : TM2ComputableAux Bool Bool) (C : ℕ) : Prop :=
  ∀ (n : ℕ) (φ : CNF n), 4 ≤ n → SatK.IsKCNF k φ → CountsWithin M k φ (timeVariables α C n)

/-- One machine with finite alphabets, and for every width k ≥ 1 a constant C, with `CountsFor`. -/
def Counts (α : ℝ) : Prop :=
  ∃ M : TM2ComputableAux Bool Bool, (∀ i, Finite (M.tm.Γ i)) ∧ ∀ k : ℕ, 1 ≤ k → ∃ C : ℕ, CountsFor α k M C

/-- `num`, given ℓ and K_ℓ in unary, returns the numerator and the denominator of a number between 0.85·ρ^ℓ
and ρ^ℓ. (For ρ > 0 the denominator is not 0, since in Lean a fraction with the denominator 0 is 0.) -/
def IsBetween (ρ : ℝ) (x₀ : ℕ) (num : U × U → ℕ × ℕ) : Prop := ∀ l : ℕ,
  0.85 * ρ ^ l ≤ ((num (List.replicate l (), List.replicate (Levels.Gen.K x₀ l) ())).1 : ℝ) / ((num (List.replicate l (), List.replicate (Levels.Gen.K x₀ l) ())).2 : ℝ) ∧
  ((num (List.replicate l (), List.replicate (Levels.Gen.K x₀ l) ())).1 : ℝ) / ((num (List.replicate l (), List.replicate (Levels.Gen.K x₀ l) ())).2 : ℝ) ≤ ρ ^ l

/-- The proviso: «a number between 0.85ρ^ℓ and ρ^ℓ can be computed from ℓ in time polynomial in
K_ℓ». -/
def Proviso (ρ : ℝ) (x₀ : ℕ) : Prop := ∃ num : U × U → ℕ × ℕ, PolyT num ∧ IsBetween ρ x₀ num

/-- «… as is the case for ρ = 11/12 and for ρ = 1/√2.» For every x₀. -/
def ProvisoHolds : Prop := ∀ x₀ : ℕ, Proviso (11 / 12) x₀ ∧ Proviso (1 / Real.sqrt 2) x₀

/-- Theorem A (c), second sentence. Suppose that there are pieces with parameters (ρ, c), let α' =
log(1/ρ), let x₀ ≥ 18 be an integer with 2^x₀ ≥ c + 5, and let the proviso hold. Then one machine
counts, for every fixed k ≥ 1, the satisfying assignments of a k-CNF
on n ≥ 4 variables within 2^{C·n·log log n/(log n)^{α'}} steps, with a constant C that may depend on
k. -/
def CountsFromPieces : Prop := ∀ (ρ : ℝ) (c x₀ : ℕ), AppRunningTime.Exist ρ c → 18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ → Proviso ρ x₀ → Counts (AppRunningTime.alpha' ρ)

/-- Theorem A, with both sentences of (c) with the printed hypotheses and quantifiers, in steps of a
Turing machine. Parts (a), (b) and (d) are those of `AppRunningTime.ThmRunningTime`, word for word. -/
structure RunningTimesFromPieces : Prop where
  /-- (a) -/
  a : ∀ (ρ : ℝ) (x₀ : ℕ), 1 / 2 ≤ ρ → ρ < 1 → 18 ≤ x₀ → AppRunningTime.PartA ρ x₀
  /-- (b); C₀ depends only on c. -/
  b : ∀ c : ℕ, ∃ C₀ : ℕ, ∀ (ρ : ℝ) (x₀ : ℕ), AppRunningTime.Exist ρ c → 18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ → AppRunningTime.PartB ρ x₀ C₀
  /-- (c), first sentence: variables need not occur -/
  c_m : ClausesOccur.CountsFromPieces
  /-- (c), second sentence: with the proviso, one machine for all k -/
  c_n : CountsFromPieces
  /-- «as is the case for ρ = 11/12 and for ρ = 1/√2» -/
  c_proviso : ProvisoHolds
  /-- (d), as in `AppRunningTime.ThmRunningTime`. The printed proof of (d) is not formalized; (d)
  follows from a bound of the same form with the larger exponent 3/19 in place of α'/10. -/
  d : ∀ (ρ : ℝ) (c : ℕ), AppRunningTime.Exist ρ c → Sat3.InRateTM (AppRunningTime.alpha' ρ / 10)

end FixedWidth
