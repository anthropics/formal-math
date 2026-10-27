/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Enumerate.Defs
public import Exits.Defs
public import Eight.SecProof_Proof

/-! # «It suffices …», for deciding, from Lemma 4 as an enumeration (definitions and statements only)

The proofs of Theorem 2 in proof/networks/Eight/, proof/threesat/ThreeSatOnTree/ and
proof/threesat/ThreeSatPrinted/ take Lemma 4 at one place, the property `Eight.SufficesSparse δ M S`
(proof/networks/Eight/SecProof_Proof.lean). It differs from the printed sentence: the machine Mc for
sparse formulas must work for EVERY number m of clauses, not only for m ≤ Mn; there is no «plus a
polynomial in n».
`SufficesPrinted δ M S` has both as printed, so it asks less of Mc and says more of S. The
construction S is `satLoop τ`, lines 1 to 4 of Algorithm 1 in their deciding form: go through the
formulas of Lemma 4 one after the other (`Enumerate.produced`: the outputs ψ ∪ 𝒩), test each with
Mc, and return «satisfiable» at the first that passes (`Exits.walkUntil`).
The last sentence of the proof, «Lemma 4 yields at most 2^{δn/3} such formulas, in time 2^{δn/3}
times a polynomial in n, … so the total time is O(2^{δn})», is `StTotal`: (number of formulas) ×
(cost of one) + (cost of the enumeration).
This file has no proofs. -/

@[expose] public section

namespace Suffices

open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat Paper SparsificationLemma Enumerate Exits

/-- **Lines 1 to 4 of Algorithm 1**, for a fixed parameter τ of Lemma 4 and a machine Mc in the
place of Count: decode the input into (n, φ); answer «unsatisfiable» if φ has an empty clause (not a
clause in the paper);
«for each Φ in the list that Lemma 4 computes from φ and ε do» (line 2), then, in place of lines 3
and 4 of the paper (which add up 2^{n'}·Count(Φ)), return "satisfiable" at the first Φ with Count(Φ) >
0 and "unsatisfiable" if there is none. The formulas are produced one at a time; the list is not
stored. -/
def satLoop (τ : ℕ) (Mc : StepMachine Formula ℤ) : StepMachine (List Bool) Bool :=
  Stepped.mapIn (decU 3) (Stepped.ite (fun p => hasNil p.2) (Stepped.const false) (walkUntil (rule τ) rootC (Stepped.mapIn SparsificationLemma.out (Stepped.mapOut Mc posZ))))

/-- What is asked of the machine Mc: to decide whether a 3-CNF Φ with m ≤ Mn clauses is satisfiable,
in time O(2^{δ'm}) plus a polynomial in n (the deciding form of the paper's sentence, which counts).
For every n and every 3-CNF Φ on n variables with m ≤ M·n clauses, Mc returns within A·2^{δ'm} +
A·(n+1)^A steps, on states of size at most A·(size Φ + n)^A, an integer that is positive exactly if
Φ is satisfiable. Nothing is asked for other Φ. -/
def DecidesSparse (δ' : ℝ) (M : ℕ) (Mc : StepMachine Formula ℤ) (A : ℕ) : Prop :=
  ∀ (n : ℕ) (Φ : Formula), Φ.Is3CNF n → Φ.length ≤ M * n →
    ∃ (T : ℕ) (v : ℤ), Mc.Runs Φ T (A * (size Φ + n) ^ A) v ∧ (0 < v ↔ Φ.Sat) ∧ (T : ℝ) ≤ A * (2 : ℝ) ^ (δ' * Φ.length) + A * ((n : ℝ) + 1) ^ A

/-- **It suffices to decide whether a 3-CNF Φ with m ≤ Mn clauses is satisfiable, in time O(2^{δ'm})
plus a polynomial in n** (the deciding form of the paper's sentence, which counts), δ' = δ/(3M), as
a property of the constant M and of a construction S of machines: S keeps polynomial-time steps, and
whenever Mc does what the sentence says, S Mc decides 3-SAT on n variables within c·2^{δn} steps. -/
def SufficesPrinted (δ : ℝ) (M : ℕ) (S : StepMachine Formula ℤ → StepMachine (List Bool) Bool) : Prop :=
  (∀ Mc : StepMachine Formula ℤ, PolyTimeSteps Mc → PolyTimeSteps (S Mc)) ∧
  ∀ (Mc : StepMachine Formula ℤ) (A : ℕ), DecidesSparse (δ / (3 * M)) M Mc A → Paper.DecidesInSteps (S Mc) δ

/-- The printed property gives `Eight.SufficesSparse`, the property that the proofs of Theorem 2
use: a machine that works for every m works for m ≤ Mn. -/
def StPrintedGivesSparse : Prop := ∀ (δ : ℝ) (M : ℕ) (S : StepMachine Formula ℤ → StepMachine (List Bool) Bool), SufficesPrinted δ M S → Eight.SufficesSparse δ (M : ℝ) S

/-- **The run of lines 1 to 4**, for an enumeration and any test: let φ be a 3-CNF on n variables
and let Mc return on every formula that is TESTED (those produced up to and including the first with
a positive result) within t steps the integer v Φ. Then `satLoop τ Mc`, started on the code of φ,
returns within
(number of formulas tested)·(t + 2) + τ⁶·n + 2 steps whether v Φ > 0 for some formula produced.
Beyond the states of Mc (of size at most Sm) the states have size polynomial in the length of the
input; the constant c does not depend on Mc, n or φ. -/
def StLoopRuns : Prop := ∀ (ε : ℝ) (M τ : ℕ), Enumerates ε M τ → ∃ c : ℕ, ∀ (Mc : StepMachine Formula ℤ) (n : ℕ) (φ : Sat3.CNF n), Sat3.Is3CNF φ → [] ∉ φ → ∀ (v : Formula → ℤ) (t Sm : ℕ),
  (∀ Φ ∈ tested (fun Φ => posZ (v Φ)) (produced τ n (Decode.toN φ)), Mc.Runs Φ t Sm (v Φ)) →
  (satLoop τ Mc).Runs (Sat3.enc φ) ((tested (fun Φ => posZ (v Φ)) (produced τ n (Decode.toN φ))).length * (t + 2) + depth τ n + 2) (c * ((Sat3.enc φ).length + 1) ^ c + Sm)
    ((produced τ n (Decode.toN φ)).any fun Φ => posZ (v Φ))

/-- **«Lemma 4 yields at most 2^{δn/3} such formulas, in time 2^{δn/3} times a polynomial in n, … so
the total time is O(2^{δn})»**: the arithmetic. N formulas, N ≤ 2^{δn/3}; each costs at most
A·2^{δ'm} + A(n+1)^A, rounded up to a whole number of steps, and 2 steps of the walk, with δ'm ≤
δn/3: together at most A·2^x + A(n+1)^A + 3 with x ≤ δn/3; the enumeration costs D·n + 2 more. -/
def StTotal : Prop := ∀ (δ : ℝ) (A D : ℕ), 0 < δ → ∃ c : ℕ, ∀ (n N : ℕ) (x : ℝ), (N : ℝ) ≤ (2 : ℝ) ^ (δ / 3 * n) → x ≤ δ / 3 * n →
  (N : ℝ) * (A * (2 : ℝ) ^ x + A * ((n : ℝ) + 1) ^ A + 3) + D * n + 2 ≤ c * (2 : ℝ) ^ (δ * n)

/-- **«By Lemma 4 with ε = δ/3, … it suffices …»**: from Lemma 4 as an enumeration
`Enumerates (δ / 3) M τ`, for its constant M = M(δ/3) and its parameter τ (not in the paper). -/
def StSuffices : Prop := ∀ (δ : ℝ) (M τ : ℕ), 0 < δ → 1 ≤ M → Enumerates (δ / 3) M τ → SufficesPrinted δ M (satLoop τ)

/-- The run of lines 1 to 4 from the walk that halts at the first leaf that passes. -/
def StLoopRunsOf : Prop := StWalkUntil → StLoopRuns

/-- The same with what it rests on in its hypotheses: the run of the loop, the count of the total
time, and (for the polynomial-time steps of the loop) those of `Exits.foldUntil`. -/
def StSufficesOf : Prop := StLoopRuns → StTotal → StFoldUntilPoly → StSuffices

end Suffices
