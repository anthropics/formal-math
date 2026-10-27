/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountKSatStatement
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Theorem 2 in its decision form, Definition 6, Corollaries 5 and 6, and the counting bound of Theorem C, as Lean propositions

Each `def … : Prop` below is a result of the paper (Theorem 2, the notions of Definition 6,
Corollaries 5 and 6, and the counting bound of Theorem C with its exponent of log n as a parameter),
as close to the paper's sentence as the vocabulary of
`ThreeSatStatement.lean`, `KSatStatement.lean` and `CountKSatStatement.lean` allows. This file has
definitions only (no theorem, no proof) and imports only
`CountKSatStatement.lean` (and through it `KSatStatement.lean`, `ThreeSatStatement.lean`) and
Mathlib. The proofs add no
mathematics: each is derived by arithmetic from an end theorem of this development.

## How to read it

Read `ThreeSatStatement.lean`, `KSatStatement.lean` and `CountKSatStatement.lean` first. From them:
* `n` is the number of variables x₀ … xₙ₋₁. An instance of k-SAT (`SatK.IsKCNF k φ`) is a list of
  clauses with at most k literals each, no clause written twice.
* «A deterministic algorithm» is a Turing machine of Mathlib (`Turing.FinTM2`: deterministic,
  finitely many stacks) all of whose alphabets are finite. Time is its number of steps.
* `SatK.DecidesTM k M t`: for EVERY n and every instance of k-SAT on n variables, M halts within
  `t n` steps with the bit «satisfiable».
  `SatK.CountsTM k M t`: the same with the number of satisfying assignments (among all 2ⁿ
  assignments), in n + 1 bits, as output.
  At k = 3, `SatK.DecidesTM 3` is `Sat3.DecidesTM` of `ThreeSatStatement.lean`.

In this file:
* `lg` is the paper's log: «log = log₂» (Section 3), real-valued.
* `DecidesInTime k n₀ T` is «a deterministic algorithm decides k-SAT on n ≥ n₀ variables in time at
  most T(n)»; `CountsInTime k n₀ T` is the same for counting.
  The machine is chosen before n. It is correct and halts for every n, also for n < n₀; only the
  bound T is claimed for n ≥ n₀ alone.
* Every O(…) of the paper is written out with a constant: «time O(f(n))» is `∃ C : ℝ`, time ≤
  C·f(n), and «time 2^{O(f(n))}» is `∃ C : ℝ`, time ≤ 2^{C·f(n)}, in both cases
  for ALL n in the paper's range (n ≥ 0 or n ≥ 2), not only for large n. The constant is chosen
  before n. There is no factor in front of 2^{C·f(n)}.
* All powers with a real exponent are Mathlib's `Real.rpow`.

## Where a sentence here differs from the paper's

* The paper counts operations on words and table queries (Section 3) without fixing a machine; here
  time is steps of a multi-stack Turing machine.
* The paper's k-CNF is a finite SET of clauses, and a clause is a nonempty set of literals; here a
  formula is a list without repetition whose clauses are lists. So the same set of
  literals in another order is another clause, a literal may be repeated inside a clause, and the
  empty clause is allowed. These are more inputs than the paper's, and all are handled.
* The input format is fixed (`SatK.enc`: n in unary, then k slots per clause); the paper fixes none.
* Definition 6 and Corollary 5 are about DETERMINISTIC machines only. The paper remarks after
  Definition 6 that the literature also allows randomized algorithms in the definition of s_k and
  that
  Corollary 5 holds under each convention, since a deterministic algorithm is a randomized one that
  uses no random bits; that remark is not formalized.
* #ETH in Corollary 6 is `SatK.CountETH_TM`, this development's rendering, for deterministic Turing
  machines, of the definition of Dell, Husfeldt, Marx, Taslaman and Wahlén that the paper cites
  (`CountKSatStatement.lean`, «Which hypothesis is negated»).
* The paper's s_k is a real number; `SatK.sTM k` takes values in [0, ∞] and is ∞ if no δ works.
  Since Corollary 5 says that it is 0, this makes no difference there.
* Of the numbered results of the paper, only Theorem 2, Definition 6, Corollaries 5 and 6 and the
  counting bound of Theorem C are stated here; the last with its exponent of log n
  as a parameter c, and for 3-CNF on n ≥ 2 variables.
* What is verified is that these SENTENCES are true; it is not verified that the paper's written
  proofs
  are correct. -/

@[expose] public section

namespace PaperSentences

open Turing
open Sat3 (CNF)
open scoped ENNReal

/-! ### Vocabulary -/

/-- The paper's log: «log = log₂». -/
noncomputable def lg (x : ℝ) : ℝ := Real.logb 2 x

/-- «A deterministic algorithm decides k-SAT on n ≥ n₀ variables in time at most T(n)»: one machine
M with finite alphabets decides every instance on n variables within
t(n) steps, for every n, and t(n) ≤ T(n) for every n ≥ n₀. -/
def DecidesInTime (k n₀ : ℕ) (T : ℕ → ℝ) : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (t : ℕ → ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ SatK.DecidesTM k M t ∧ ∀ n : ℕ, n₀ ≤ n → (t n : ℝ) ≤ T n

/-- «A deterministic algorithm computes the number of satisfying assignments of a k-CNF on n ≥ n₀
variables in time at most T(n)». -/
def CountsInTime (k n₀ : ℕ) (T : ℕ → ℝ) : Prop :=
  ∃ (M : TM2ComputableAux Bool Bool) (t : ℕ → ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ SatK.CountsTM k M t ∧ ∀ n : ℕ, n₀ ≤ n → (t n : ℝ) ≤ T n

/-! ### Theorem 2 -/

/-- Theorem 2 in its decision form: «For every δ > 0 there is a deterministic algorithm that»
decides 3-SAT «on n variables, with any number of clauses, in time O(2^{δn}).» -/
def ThmEveryDelta : Prop := ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, DecidesInTime 3 0 fun n => C * (2 : ℝ) ^ (δ * n)

/-! ### Definition 6 and Corollary 5 -/

/-- Definition 6: «Let s_k be the infimum of all δ ≥ 0 such that some deterministic algorithm
decides k-SAT on n variables in time O(2^{δn})» is `SatK.sTM k` of
`KSatStatement.lean`. «… and let s_∞ = sup_{k≥3} s_k.» -/
noncomputable def sInfty : ℝ≥0∞ := ⨆ (k : ℕ) (_ : 3 ≤ k), SatK.sTM k

/-- Definition 6: «The Exponential Time Hypothesis (ETH) is the statement that s_k > 0 for all k ≥ 3.» -/
def ETH : Prop := ∀ k : ℕ, 3 ≤ k → 0 < SatK.sTM k

/-- Definition 6: «The Strong Exponential Time Hypothesis (SETH) is the statement s_∞ = 1.» -/
def SETH : Prop := sInfty = 1

/-- Corollary 5. «s_k = 0 for every k ≥ 3. Hence s_∞ = 0, and both ETH and SETH are false.» -/
def CorEth : Prop := (∀ k : ℕ, 3 ≤ k → SatK.sTM k = 0) ∧ sInfty = 0 ∧ ¬ ETH ∧ ¬ SETH

/-! ### Corollary 6 -/

/-- Corollary 6. «For every k ≥ 3 and δ > 0 there is a deterministic algorithm that computes the
number of satisfying assignments of a k-CNF on n variables in time
O(2^{δn}). For k = 3 this says that the counting version #ETH of ETH is false.» (#ETH is
`SatK.CountETH_TM` of `CountKSatStatement.lean`.) -/
def CorCounting : Prop :=
  (∀ k : ℕ, 3 ≤ k → ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, CountsInTime k 0 fun n => C * (2 : ℝ) ^ (δ * n)) ∧ ¬ SatK.CountETH_TM

/-! ### The running time as a function of n: Theorem C -/

/-- Theorem C with its exponent α/10 of log n replaced by a parameter c: one deterministic algorithm
computes the number of satisfying assignments of a 3-CNF on n ≥ 2 variables in time 2^{O(n/(log
n)^c)}. -/
def CountRate (c : ℝ) : Prop := ∃ C : ℝ, CountsInTime 3 2 fun n => (2 : ℝ) ^ (C * (n / lg n ^ c))

end PaperSentences
