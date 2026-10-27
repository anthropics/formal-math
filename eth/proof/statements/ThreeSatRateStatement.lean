/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSatStatement
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Definitions: ONE Turing machine decides 3-SAT on n variables, for all n, within C·2^{C·n/(log₂(n+2))^c} steps, or A·2^{δn} for every δ > 0

What it means that ONE Turing machine decides 3-SAT on n variables within 2^{O(n/(log n)^c)} steps,
in the vocabulary of
`ThreeSatStatement.lean`. This file has definitions only (no theorem, no proof) and imports only
`ThreeSatStatement.lean` and Mathlib.

## How to read it, for a reader who knows complexity theory but little Lean

From `ThreeSatStatement.lean` (read that file first):
* `n` is the NUMBER OF VARIABLES x₀ … xₙ₋₁, not the length of the input. An instance (`Is3CNF φ`) is
  a list of clauses with at most
  3 literals each and no clause written twice, so it has at most (2n+1)³ clauses.
* `enc φ` is the input string over {0,1}: n in unary (1ⁿ0), then 3 slots per clause, each slot a
  literal (or «empty») as a binary
  number of ⌊log₂(2n)⌋+1 bits, low bit first. Its length is O(n³ log n).
* A machine is Mathlib's `Turing.FinTM2`: deterministic, finitely many labels and states, and
  finitely many STACKS, one of them for the
  input and one (possibly the same) for the output. Two stacks make a tape and a tape makes a stack,
  so its time is that of multitape
  Turing machines up to a constant factor (standard; not proved here). `TM2ComputableAux Bool Bool`
  is such a machine together with
  bijections between {0,1} and the alphabets of its input stack and of its output stack. So those
  two alphabets are finite; Mathlib
  does not ask this of the other stacks, so the definitions below do: `∀ k, Finite (M.tm.Γ k)`.
* `DecidesTM M t` says: for EVERY n and EVERY instance φ on n variables, M started on `enc φ` halts
  within `t n` steps, with the one bit
  «φ is satisfiable» on its output stack, all other stacks empty, and its internal state back at the
  initial one. A step is one
  `TM2.step`: it runs the finite statement at the current label as far as the first `goto` or `halt`
  it reaches. For a fixed machine
  that is a bounded number of pushes and pops.

In this file:
* The order of the quantifiers is the point. In `InRateTM c` the machine `M` and the constant `C`
  are chosen FIRST (`∃ M C`), and then the
  bound holds for all n (the `∀ n` is inside `DecidesTM`). So neither M nor C depends on n, or on
  any δ. In `InTimeTM δ` of
  `ThreeSatStatement.lean` the machine may be a different one for each δ.
* Logarithms are to base 2 and real-valued, and are taken of n+2, not of n, so that log₂(n+2) ≥ 1
  for every n ≥ 0: nothing is divided
  by 0 and no case n = 0, 1 is left out. For large n this changes nothing, since log₂(n+2)/log₂ n → 1.
* All powers, `2 ^ (…)` and `(…) ^ c`, have real exponents (Mathlib's `Real.rpow`), and in
  `InRateTM (3 / 19)` the 3/19 is a division of
  real numbers. `⌊x⌋₊` rounds x ≥ 0 down to a natural number; a number of steps is whole, so this
  changes nothing. The exponent 3/19 is not one that the paper states (Theorem A gives α'/10 for
  3-SAT).

## What the statement does not say

* The bound holds for every n, but it says something only for very large n, and C is not explicit.
  For c = 3/19 and any C ≥ 2 the
  bound is at least 2ⁿ whenever log₂(n+2) ≤ 2^6. The machine of the proof
  (in proof/rates/PaddedDescent/) is exhaustive search for every n < 2^(2^518). This is not a
  practical algorithm.
* `¬ ETH_TM` alone allows a different machine for each δ > 0. The statements here are stronger: ONE
  machine for all δ, and in `InRateTM` a rate. -/

@[expose] public section

namespace Sat3

open Turing
open scoped NNReal

/-- The time bound C·2^{C·n/(log₂(n+2))^c}, rounded down. The same C serves as the factor in front
and as the factor in the exponent,
which loses nothing: two constants can be replaced by their maximum. -/
noncomputable def rateBound (C : ℕ) (c : ℝ) (n : ℕ) : ℕ :=
  ⌊(C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * n / (Real.logb 2 ((n : ℝ) + 2)) ^ c)⌋₊

/-- «3-SAT is in time 2^{O(n/(log n)^c)}» on Turing machines: one machine, finite alphabets, one
constant C, all n. -/
def InRateTM (c : ℝ) : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (C : ℕ), (∀ k, Finite (M.tm.Γ k)) ∧ DecidesTM M (rateBound C c)

/-- «3-SAT is in time 2^{o(n)}», without a rate.
The SAME machine meets A·2^{δn} for every δ > 0; only the constant A depends on δ. -/
def SubexpTM : Prop :=
  ∃ M : TM2ComputableAux Bool Bool, (∀ k, Finite (M.tm.Γ k)) ∧
    ∀ δ : ℝ≥0, 0 < δ → ∃ A : ℕ, DecidesTM M fun n => ⌊(A : ℝ) * (2 : ℝ) ^ ((δ : ℝ) * n)⌋₊

end Sat3
