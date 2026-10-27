/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import KSatStatement
public import Mathlib.Data.Fintype.Pi

/-! # The statement for #k-SAT and for the counting Exponential Time Hypothesis

What «the number of satisfying assignments of a k-CNF on n variables can be computed in time
O(2^{δn})» and «#ETH» mean here, in the vocabulary of
`ThreeSatStatement.lean` and `KSatStatement.lean`. This file has definitions only (no theorem, no
proof) and imports only `KSatStatement.lean` (and Mathlib).

## How to read it, for a reader who knows complexity theory but little Lean

Read `ThreeSatStatement.lean` and `KSatStatement.lean` first. `CNF`, `IsKCNF` and `enc` are taken
from them unchanged: the instances and their codes are those of k-SAT.
* `n` is the NUMBER OF VARIABLES x₀ … xₙ₋₁, not the length of the input.
* `numSat φ` counts among ALL 2ⁿ assignments to x₀ … xₙ₋₁. A variable that does not occur in φ
  doubles the count. The formula without clauses has the
  count 2ⁿ, a formula with an empty clause has the count 0. At n = 0 there is one assignment, the
  empty one.
* The count lies between 0 and 2ⁿ, both included, so it needs n + 1 bits. `binary n N` is the word
  of exactly n + 1 bits of N, LOWEST BIT FIRST, the
  convention of `enc`, with zeros at the end if N is small. On the numbers 0 … 2ⁿ it is one-to-one.
* `CountsTM k M t` says: for EVERY n and EVERY instance φ of k-SAT on n variables, M started on
  `enc k φ` halts within `t n` steps with the word
  `binary n (numSat φ)` as its output: the lowest bit on top of the output stack, all other stacks
  empty, and the internal state back at the initial one.
  Machines, steps and the demand for finite alphabets are as in `KSatStatement.lean`.
* In `CountInTimeTM k δ` the machine and the constant c may depend on k and on δ.
* At k = 0 the formulas [] and [[]] have the same code but the counts 2ⁿ and 0, so
  `CountInTimeTM 0 δ` is false for a reason that has nothing to do with time (see
  `KSatStatement.lean`).

## Which hypothesis is negated

#ETH is from Dell, Husfeldt, Marx, Taslaman and Wahlén, «Exponential time complexity of the permanent and the Tutte polynomial» (ACM Transactions on
Algorithms, doi 10.1145/2635812; arXiv 1206.1775): «There is a constant c > 0 such that no
deterministic algorithm can compute #3-SAT in time exp(c·n).» `CountETH_TM` is this
sentence with 2^{δn} for exp(c·n), δ = c/ln 2, and with a constant factor allowed in the time bound,
which makes the hypothesis stronger for a given δ and changes nothing
once δ ranges over all positive numbers.
An instance here has AT MOST 3 literals per clause, which includes the formulas with exactly 3.
The literature speaks of algorithms on any reasonable model, usually random-access machines. A
multi-stack Turing machine can be simulated on a unit-cost
random-access machine with constant overhead, so a fast Turing machine is a fast algorithm there too
(standard; not proved here). A deterministic machine is a
special randomized one, so `CountInTimeTM 3 δ` for every δ > 0 also contradicts the same sentence
about randomized algorithms.

## What the statement does not say

* No single machine for all δ, and no rate 2^{o(n)}: a separate machine for every pair (k, δ). Some
  texts, among them an abstract of the paper just cited, word #ETH as
  «the satisfying assignments cannot be counted in time exp(o(n))», which speaks of one algorithm.
  That hypothesis follows from the one negated here, so it is not
  refuted by this.
* The time is bounded in n alone, which makes sense only because no clause is written twice
  (`IsKCNF`). Writing a clause twice does not change the count. For inputs with
  repeated clauses the usual convention is time O(2^{δn})·poly(length of the input); removing the
  repetitions first costs polynomial time (standard; not proved here).
* The hypothesis with the number m of clauses in place of n («not in time exp(c·m)») is not stated
  here. By Theorem 1.1 of the paper just cited it is equivalent to #ETH.
  To refute it from `CountInTimeTM 3 δ` for every δ > 0 takes only the easy direction: at most 3m
  variables occur, and each of the others doubles the count (standard; not proved here).
* Nothing about weighted counting, about counting modulo a number, or about formulas of unbounded
  width.
* That a machine which counts can be turned into a machine which decides is not formalized; deciding
  is the subject of `KSatStatement.lean`.
* The constants are not explicit. -/

@[expose] public section

namespace SatK

open Turing
open Sat3 (CNF)
open scoped NNReal ENNReal

/-- The number of satisfying assignments of φ: among all 2ⁿ assignments to x₀ … xₙ₋₁, how many make
a literal of every clause true. -/
def numSat {n : ℕ} (φ : CNF n) : ℕ := (Finset.univ.filter fun a : Fin n → Bool => ∀ C ∈ φ, ∃ l ∈ C, a l.1 = l.2).card

/-- The number N as a word of n + 1 bits, lowest bit first. -/
def binary (n N : ℕ) : List Bool := (List.range (n + 1)).map N.testBit

/-- `M`, started on the code of an instance of k-SAT, halts within `t n` steps with the number of
satisfying assignments, in n + 1 bits, as output. -/
def CountsTM (k : ℕ) (M : TM2ComputableAux Bool Bool) (t : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (φ : CNF n), IsKCNF k φ →
    Nonempty (TM2OutputsInTime M.tm ((enc k φ).map M.inputAlphabet.invFun)
      (some ((binary n (numSat φ)).map M.outputAlphabet.invFun)) (t n))

/-- «#k-SAT is in time O(2^{δn})» on Turing machines: one machine, finite alphabets, one constant. -/
def CountInTimeTM (k : ℕ) (δ : ℝ≥0) : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (c : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    CountsTM k M fun n => ⌊(c : ℝ) * (2 : ℝ) ^ ((δ : ℝ) * n)⌋₊

/-- #ETH on Turing machines: for some δ > 0, #3-SAT is not in time O(2^{δn}). -/
def CountETH_TM : Prop := ∃ δ : ℝ≥0, 0 < δ ∧ ¬ CountInTimeTM 3 δ

end SatK
