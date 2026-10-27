/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSatStatement

/-! # k-SAT in time O(2^{δn}) and the numbers s_k

What «k-SAT on n variables is in time O(2^{δn})» and the numbers s_k of the Strong Exponential Time
Hypothesis mean here, in the vocabulary of `ThreeSatStatement.lean`. This file has definitions only
(no theorem, no proof) and imports only `ThreeSatStatement.lean` (and through it Mathlib).

## How to read it, for a reader who knows complexity theory but little Lean

Read `ThreeSatStatement.lean` first. `Lit`, `CNF`, `Satisfiable` and `slot` are taken from it
unchanged. `IsKCNF`, `enc`, `DecidesTM`, `InTimeTM` and `sTM` are
that file's definitions with the width 3 replaced by a parameter k; at k = 3 they are literally the
same.
* `n` is the NUMBER OF VARIABLES x₀ … xₙ₋₁, not the length of the input.
* An instance of k-SAT (`IsKCNF k φ`) is a list of clauses with at most k literals each and no
  clause written twice. A literal may be repeated
  inside a clause, a clause may hold x and ¬x, the empty clause is allowed, and the same set of
  literals written in another order counts as another
  clause. So there are at most (2n+1)^k clauses.
* `enc k φ` is the input over {0,1}: n in unary (1ⁿ0), then k slots per clause, each slot a literal
  (or «empty») as a binary number of
  ⌊log₂(2n)⌋+1 bits, low bit first. Its length is at most n + 1 + (2n+1)^k·k·(⌊log₂(2n)⌋+1):
  polynomial in n for fixed k.
* A machine is Mathlib's `Turing.FinTM2`: deterministic, finitely many labels and states, finitely
  many stacks. Mathlib does not ask that every stack has
  a finite alphabet, so `InTimeTM` does: `∀ i, Finite (M.tm.Γ i)`. `DecidesTM k M t` says: for EVERY
  n and EVERY instance φ of k-SAT on n variables, M started
  on `enc k φ` halts within `t n` steps with the one bit «φ is satisfiable» as its output, all other
  stacks empty and its internal state back at the initial one. One step runs the statement at the
  current label as far as a `goto` or `halt`: a bounded number of pushes and pops for a fixed
  machine.
* In `InTimeTM k δ` the machine and the constant c may depend on k and on δ, as in the usual
  definition of the numbers s_k.
* **Why k ≥ 1 everywhere.** At k = 0 a clause takes no bits, so the formula without clauses (satisfiable)
  and the formula whose only clause is the
  empty one (unsatisfiable) have the same code 1ⁿ0, and no machine can tell them apart:
  `InTimeTM 0 δ` is false for a reason that has nothing to do
  with time. A hypothesis stated with these definitions should therefore speak of k ≥ 1 only. The
  literature speaks of k ≥ 3; a hypothesis about some k ≥ 3 implies the
  one about some k ≥ 1, so refuting the form with k ≥ 1 refutes the usual form too.

## Which hypothesis is negated

The numbers s_k and their limit s_∞ are from Impagliazzo and Paturi, «On the complexity of k-SAT»,
JCSS 62 (2001), who ask whether s_∞ = 1. The
name SETH, for s_∞ = 1, is from Calabro, Impagliazzo and Paturi, «The complexity of satisfiability
of small depth circuits» (2009). The sources differ in the
algorithms they allow in the definition of s_k (deterministic or randomized). Here s_k (`sTM k`) is
defined with DETERMINISTIC Turing machines. A deterministic machine is a
special randomized one, so «for every k ≥ 1 and δ > 0 a deterministic machine decides k-SAT in time
O(2^{δn})» puts s_k = 0 under either definition.
The literature speaks of algorithms on any reasonable model, usually random-access machines. A
multi-stack Turing machine can be simulated on a
unit-cost random-access machine with constant overhead, so a fast Turing machine is a fast algorithm
there too (standard; not proved here).
In this vocabulary SETH reads: for every δ < 1 some k-SAT, k ≥ 1, is not in time O(2^{δn}); through
the s_k, it says that the supremum of the `sTM k`, k ≥ 1, is at
least 1. (`sTM k` is ∞ if no δ works, so «the supremum equals 1» would be the wrong thing to negate:
a single s_k = ∞ would already make it false.)

## What these definitions do not say

* Nothing about CNF-SAT with clauses of unbounded width: k is fixed before the machine is chosen.
  Many papers also call «CNF-SAT on n variables and m
  clauses is not in time 2^{(1-ε)n}·poly(m)» by the name SETH. That hypothesis follows from the one
  described above, so it is not refuted by refuting that one.
* The time is bounded in n alone, which makes sense only because no clause is written twice. For
  inputs with repeated clauses the usual convention is time
  O(2^{δn})·poly(length of the input); removing the repetitions first costs polynomial time
  (standard; not proved here).
* No single machine for all δ, and no rate 2^{o(n)} for k-SAT: a separate machine for every pair (k,
  δ). The constants are not explicit.
* The implication «SETH implies ETH» of Impagliazzo, Paturi and Zane (JCSS 63 (2001)), as a
  statement about arbitrary machines, is not formalized.
  The proof in proof/consequences/WidthK/ does not reduce k-SAT to 3-SAT. It proves a sparsification
  lemma for width k, after the one of Impagliazzo, Paturi and Zane, and runs the algorithm of this
  development on k-CNF formulas directly. -/

@[expose] public section

namespace SatK

open Turing
open Sat3 (Lit CNF Satisfiable slot)
open scoped NNReal ENNReal

/-- An instance of k-SAT: at most k literals per clause, and no clause written twice, so that its
length is bounded in terms of n. -/
def IsKCNF (k : ℕ) {n : ℕ} (φ : CNF n) : Prop := (∀ C ∈ φ, C.length ≤ k) ∧ φ.Nodup

/-- As a bit string: 1ⁿ 0, then k slots per clause, ⌊log₂ (2n)⌋ + 1 bits per slot, low bit first. -/
def enc (k : ℕ) {n : ℕ} (φ : CNF n) : List Bool :=
  List.replicate n true ++ false :: φ.flatMap fun C => (List.range k).flatMap fun j =>
    (List.range (Nat.log2 (2 * n) + 1)).map (slot C[j]?).testBit

/-- `M`, started on the code of an instance of k-SAT, halts within `t n` steps with the bit
«satisfiable» as output. -/
def DecidesTM (k : ℕ) (M : TM2ComputableAux Bool Bool) (t : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (φ : CNF n), IsKCNF k φ → ∃ b : Bool, (b = true ↔ Satisfiable φ) ∧
    Nonempty (TM2OutputsInTime M.tm ((enc k φ).map M.inputAlphabet.invFun)
      (some ([b].map M.outputAlphabet.invFun)) (t n))

/-- «k-SAT is in time O(2^{δn})» on Turing machines: one machine, finite alphabets, one constant. -/
def InTimeTM (k : ℕ) (δ : ℝ≥0) : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (c : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
    DecidesTM k M fun n => ⌊(c : ℝ) * (2 : ℝ) ^ ((δ : ℝ) * n)⌋₊

/-- s_k: the infimum of the δ for which k-SAT is in time O(2^{δn}) on Turing machines (∞ if there is
no such δ). -/
noncomputable def sTM (k : ℕ) : ℝ≥0∞ := ⨅ (δ : ℝ≥0) (_ : InTimeTM k δ), (δ : ℝ≥0∞)

end SatK
