/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import MainTheoremFormsStatement
public import AppRunningTimeStatement
public import VariableBound.Printed.ThmVariablesADefs
public import RecursionWithPieces.Defs
public import TwoMachines.Defs
public import UniformInK.Top.Defs
public import GeneralPieces.Num.Between

/-! # Theorem D (b) from Theorem D (a): definitions and statements

**The text.** Theorem D (b): «The pairs (K_ℓ, e_ℓ) of (40), for the pieces of Appendix B, satisfy
this hypothesis, and e_ℓ = Θ((log K_ℓ)^(−1/2)). So there are a deterministic algorithm and an
absolute constant C such that, for all integers k ≥ 1 and n ≥ 4, the algorithm computes the number
of
satisfying assignments of a k-CNF on n variables in time 2^{C·k²·n·log log n/√(log n)}.» Step 6 of
the proof, sentence by sentence:
(1) «By Theorem B, Theorem A applies with ρ = 1/√2 and α′ = 1/2.» (2) «That its pairs satisfy the
    hypothesis of Theorem D (a) is checked in the proof of Theorem A (c).» (3) «By Theorem A (a) and
    its proof, ½ρ^ℓ ≤ e_ℓ ≤ 0.85ρ^ℓ and x₀2^ℓ ≤ log K_ℓ ≤ (3x₀+6)2^ℓ, so e_ℓ = Θ((log K_ℓ)^(−1/2)).»
(4) «Here the constants of the hypothesis are absolute, because the constant c of Theorem B is.» (5)
    «So for n ≥ K₀^17 and 3 ≤ k ≤ (log n)^(1/4) the algorithm of Theorem D (a) takes time
    2^{O(k²·n·log log n/√(log n))} with an absolute constant.» (6) «As in Step 5, k is the largest
    number of literals in a clause, or 3 if that is
larger, which multiplies k² by at most 9.» (7) «In the other cases, that is, if n < K₀^17 or this k
exceeds (log n)^(1/4), the algorithm tries all assignments; as there are fewer than (2n+1)^k ≤
n^(2k) clauses, this takes time 2^n·n^{O(k)}, reading the input included.»
(8) «It is within the bound: log n ≤ n/√(log n) ≤ n·log log n/√(log n) for n ≥ 4, so k·log n ≤
    k²·n·log log n/√(log n); if k > (log n)^(1/4), then k²·n·log log n/√(log n) ≥ n·log log n ≥ n;
    and if n < K₀^17, then n·log log n/√(log n) ≥ n/√(17·log K₀).»

**Elsewhere.** `MainTheoremForms.ThmVariablesB` also follows from the joining theorem
(`RecursionWithPieces.tiedAllCal`), which proves Step 6 for a named function directly.

**What is stated here.**
* `ThePairsSatisfyTheHypothesis`: sentences (1), (2), (4). For ALL pieces with parameters (1/√2, c),
  the named solver `RecursionWithPieces.solverAB` (the recursion of Appendix A on them) has a
  sequence of levels in the sense of the hypothesis of `MainTheoremForms.ThmVariablesA`, with K_ℓ
  and e_ℓ the numbers of display (40) at ρ = 1/√2 and x₀ = `GeneralPieces.x₀Of c`, the level is
  picked by the named program `RecursionWithPieces.pickAB`, the solver is polynomial-time, a number
  in [e_ℓ, 2e_ℓ] is computed, and the constants depend on c alone (sentence (4)).
* `ThetaOfThePairs`: sentence (3), its four inequalities and the two-sided bound with explicit
  constants.
* `MainRegimeBound`: sentence (5), for EVERY machine with the conclusion of (a).
* `widthOr3`, `RewritesAtWidthOr3`, `TestsTheMainRegime`: sentences (6), (7): the front end and the
  test of the algorithm of Step 6.
* `TriesAllWithin Mb c`, `ExhaustiveMachineExists`: sentence (7): a machine that counts within
  2^{c·n}·n^{c·k} steps.
* `FallBackIsWithinTheBound`: sentence (8), the printed inequalities.
* `EveryChoiceMeetsThmVariablesB` (the main statement): for EVERY solver with a sequence of levels
  with e_ℓ ≤ a/√(log K_ℓ), EVERY machine M with the conclusion of (a) for it, and EVERY machine Mb
  that tries all assignments within 2^{c·n}·n^{c·k} steps: EVERY machine N that chooses between M
  (on the code rewritten at this k) and Mb by the printed test meets the bound of (b).
* `ThmVariablesBFromThmVariablesA`: existence and the main statement in one.
  `ThmVariablesAImpliesThmVariablesB`: the implication between the propositions.

**What differs from the text.** The hypothesis of (a) is Lean's (cost as the length of a padding
string; see proof/variables/VariableBound/Printed/ThmVariablesADefs.lean). The choice costs a power
q, and exhaustive counting on Mathlib's machine takes 2^{c·n}·n^{c·k} steps where the text has
2^n·n^{O(k)} operations; both go into C. K₀ depends on the pieces, which are arbitrary, so the test
has K₀ as a parameter. -/

@[expose] public section

namespace PairsToBound

open Turing Groundwork PaddedDescent.F ClauseBound.Alg Wrap TwoMachines MainTheoremForms
open Sat3 (CNF)

/-! ### Sentences (1) to (4): the pairs -/

/-- «… a number in [e_ℓ, 2e_ℓ] can be computed from ℓ in time polynomial in K_ℓ» (Theorem D (a),
hypothesis). `num` is polynomial-time in (ℓ in unary, K_ℓ in unary) and returns the numerator and
the denominator of a number in [e_ℓ, 2e_ℓ]. -/
def NumberBetween {Idx : Type} [Enc Idx] (S : Solver Idx) {e : ℕ → ℝ} {C₀ : ℕ} (Q : S.Seq e C₀) (num : U × U → ℕ × ℕ) : Prop :=
  PolyT num ∧ ∀ l : ℕ,
    e l ≤ ((num (List.replicate l (), List.replicate (S.K (Q.idx l)) ())).1 : ℝ) / ((num (List.replicate l (), List.replicate (S.K (Q.idx l)) ())).2 : ℝ) ∧
    ((num (List.replicate l (), List.replicate (S.K (Q.idx l)) ())).1 : ℝ) / ((num (List.replicate l (), List.replicate (S.K (Q.idx l)) ())).2 : ℝ) ≤ 2 * e l

/-- «That its pairs satisfy the hypothesis of Theorem D (a) is checked in the proof of Theorem A
(c)»; there: «Its hypothesis holds by (a) and (b), with the larger of C₀ and 10». The general form,
for every ρ and x₀ of Theorem A: for every c there is a C₀, which depends on c alone, such that for
ALL pieces with parameters (ρ, c) and every x₀ ≥ 18 with 2^x₀ ≥ c + 5 the named solver, the
recursion of Theorem A (b) on these pieces, is polynomial-time and has a sequence Q of levels in the
sense of the hypothesis of Theorem D (a) for the numbers K_ℓ, e_ℓ of display (40), with the constant
C₀, and the level is picked by the named program `ClauseBound.Gen.Pick.pick`. -/
def TheRecursionHasLevels : Prop :=
  ∀ c : ℕ, ∃ C₀ : ℕ, ∀ (ρ : ℝ) (x₀ : ℕ) (P : PiecesF) (A : (lam : ℕ) → ℕ → Pieces.Four lam) (val : AppRunningTime.ValQ → ℤ), AppRunningTime.IsPieces ρ c P A val → 18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ →
    ∃ Q : (solverOf (GeneralPieces.Tied.recOf P val c)).Seq (Levels.Gen.e ρ x₀) C₀,
      (solverOf (GeneralPieces.Tied.recOf P val c)).Poly ∧
      (∀ l : ℕ, (solverOf (GeneralPieces.Tied.recOf P val c)).K (Q.idx l) = Levels.Gen.K x₀ l) ∧ Q.pick = ClauseBound.Gen.Pick.pick (GeneralPieces.Tied.recOf P val c) x₀

/-- The fraction for ρ = 1/√2: 2^(−ℓ/2) for even ℓ and (7/5)·2^(−(ℓ+1)/2) for odd ℓ, a number
between 0.85ρ^ℓ and ρ^ℓ (`GeneralPieces.Between.num`, `den`). It does not look at K_ℓ. -/
def fractionHalf (p : U × U) : ℕ × ℕ := (GeneralPieces.Between.num p.1.length, GeneralPieces.Between.den p.1.length)

/-- «The pairs (K_ℓ, e_ℓ) of (40), for the pieces of Appendix B, satisfy this hypothesis»; «Here the
constants of the hypothesis are absolute, because the constant c of Theorem B is.» For every c there
are constants C₀ and Cp, which depend on c alone, such that for ALL P₀, A, val that are pieces with
parameters (1/√2, c) as Appendix A defines them (those of
Appendix B are such pieces) there is a sequence Q of levels of the solver
`RecursionWithPieces.solverAB P₀ val c`, the recursion of Appendix A on them, for the numbers e_ℓ =
`Levels.Gen.e (1/√2) x₀ ℓ`, x₀ = `GeneralPieces.x₀Of c` (the least integer with x₀ ≥ 18 and 2^x₀ ≥ c + 5),
with the constant C₀, such that: the solver is polynomial-time; K at the ℓ-th index is K_ℓ =
`Levels.Gen.K x₀ ℓ`; the level is
picked by `RecursionWithPieces.pickAB P₀ val c`; `fractionHalf` computes a number in [e_ℓ, 2e_ℓ],
the printed clause; and ℓ ↦ ℓ + 1 is a precision with the constant Cp.
The fields of Q are the rest of the hypothesis of Theorem D (a): K_ℓ ≥ 2, K_ℓ < K_(ℓ+1) ≤ K_ℓ^C₀,
(log K_ℓ)^(−C₀) ≤ e_ℓ ≤ 1, the solver is right when the padding string has 2^need units, and need ≤
e_ℓK_ℓ²λ + C₀K_ℓ²·log(K_ℓ(λ+B)).
The LAST clause is not the paper's: it is what `MainTheoremForms.ThmVariablesA`, Lean's statement of
Theorem D (a), takes in place of the number in [e_ℓ, 2e_ℓ]. With s = ℓ + 1 the ε = 2^(−s) of that
form is about e_ℓ², not between e_ℓ and 2e_ℓ; `MainTheoremForms.Precision` allows this because it
only asks 2^(−s) ≤ e_ℓ and 2^s ≤ (2/e_ℓ)^Cp. -/
def ThePairsSatisfyTheHypothesis : Prop :=
  ∀ c : ℕ, ∃ C₀ Cp : ℕ, ∀ (P₀ : PiecesF) (A : (lam : ℕ) → ℕ → Pieces.Four lam) (val : AppRunningTime.ValQ → ℤ), AppRunningTime.IsPieces (1 / Real.sqrt 2) c P₀ A val →
    ∃ Q : (RecursionWithPieces.solverAB P₀ val c).Seq (Levels.Gen.e (1 / Real.sqrt 2) (GeneralPieces.x₀Of c)) C₀,
      (RecursionWithPieces.solverAB P₀ val c).Poly ∧
      (∀ l : ℕ, (RecursionWithPieces.solverAB P₀ val c).K (Q.idx l) = Levels.Gen.K (GeneralPieces.x₀Of c) l) ∧ Q.pick = RecursionWithPieces.pickAB P₀ val c ∧
      NumberBetween (RecursionWithPieces.solverAB P₀ val c) Q fractionHalf ∧
      Precision (Levels.Gen.e (1 / Real.sqrt 2) (GeneralPieces.x₀Of c)) RecursionWithPieces.prec Cp

/-- «By Theorem A (a) and its proof, ½ρ^ℓ ≤ e_ℓ ≤ 0.85ρ^ℓ and x₀2^ℓ ≤ log K_ℓ ≤ (3x₀+6)2^ℓ, so e_ℓ =
Θ((log K_ℓ)^(−1/2)).» For ρ = 1/√2, every x₀ ≥ 18 and every ℓ: the four inequalities, and
½·√x₀/√(log K_ℓ) ≤ e_ℓ ≤ 0.85·√(3x₀+6)/√(log K_ℓ). -/
def ThetaOfThePairs : Prop :=
  ∀ x₀ l : ℕ, 18 ≤ x₀ →
    1 / 2 * (1 / Real.sqrt 2) ^ l ≤ Levels.Gen.e (1 / Real.sqrt 2) x₀ l ∧ Levels.Gen.e (1 / Real.sqrt 2) x₀ l ≤ 0.85 * (1 / Real.sqrt 2) ^ l ∧
    (x₀ : ℝ) * 2 ^ l ≤ lg (Levels.Gen.K x₀ l) ∧ lg (Levels.Gen.K x₀ l) ≤ (3 * x₀ + 6) * 2 ^ l ∧
    1 / 2 * Real.sqrt x₀ / Real.sqrt (lg (Levels.Gen.K x₀ l)) ≤ Levels.Gen.e (1 / Real.sqrt 2) x₀ l ∧
    Levels.Gen.e (1 / Real.sqrt 2) x₀ l ≤ 0.85 * Real.sqrt (3 * x₀ + 6) / Real.sqrt (lg (Levels.Gen.K x₀ l))

/-! ### Sentence (5): the main regime -/

/-- «So for n ≥ K₀^17 and 3 ≤ k ≤ (log n)^(1/4) the algorithm of Theorem D (a) takes time
2^{O(k²·n·log log n/√(log n))}». For every solver S with a sequence Q of levels and every natural
number a with e_ℓ ≤ a/√(log K_ℓ) for all ℓ, EVERY machine M and constant C′ with the conclusion of
Theorem D (a) (`MainTheoremForms.ThmVariablesAFor`): there is a C such
that for all n ≥ K₀^17, all k with 3 ≤ k ≤ (log n)^(1/4) and every k-CNF φ on n variables the same M
counts the satisfying assignments of φ within 2^{C·k²·n·log log n/√(log n)} steps. -/
def MainRegimeBound : Prop :=
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀) (a : ℕ), (∀ l : ℕ, e l ≤ a / Real.sqrt (lg (S.K (Q.idx l)))) →
    ∀ (M : TM2ComputableAux Bool Bool) (C' : ℕ), ThmVariablesAFor S Q M C' →
      ∃ C : ℕ, ∀ (k n : ℕ) (φ : CNF n), S.K (Q.idx 0) ^ 17 ≤ n → 3 ≤ k → (k : ℝ) ^ 4 ≤ lg n → SatK.IsKCNF k φ → CountsWithin M k φ (timeN C k n)

/-! ### Sentences (6) and (7): the algorithm of Step 6 -/

/-- «k is the largest number of literals in a clause, or 3 if that is larger». -/
def widthOr3 {n : ℕ} (φ : CNF n) : ℕ := (φ.map List.length).foldr max 3

/-- φ is a k-CNF for k = `widthOr3 φ` if it has no clause twice; this k is at least 3; and it is at
most max(k, 3) for every k for which φ is a k-CNF, «which multiplies k² by at most 9». -/
def WidthOr3Stmt : Prop :=
  ∀ (n : ℕ) (φ : CNF n), 3 ≤ widthOr3 φ ∧ (φ.Nodup → SatK.IsKCNF (widthOr3 φ) φ) ∧
    ∀ k : ℕ, 1 ≤ k → SatK.IsKCNF k φ → widthOr3 φ ≤ max k 3 ∧ widthOr3 φ ^ 2 ≤ 9 * k ^ 2

/-- «the bound increases with k» (Step 5): for n ≥ 4 and k ≤ k′ the time 2^{C·k²·n·log log n/√(log
n)} at k is at most that at k′; for 3 ≤ k ≤ k′ and 0 < e ≤ 1 the same holds of
2^{C·k²·e·n·log(k/e)}. -/
def TheBoundIncreasesWithTheWidth : Prop :=
  (∀ C k k' n : ℕ, 4 ≤ n → k ≤ k' → timeN C k n ≤ timeN C k' n) ∧
  ∀ (C k k' n : ℕ) (e : ℝ), 3 ≤ k → k ≤ k' → 0 < e → e ≤ 1 → timeVariablesA C k n e ≤ timeVariablesA C k' n e

/-- `pre` maps the code of (k, φ) to the code of (`widthOr3 φ`, φ), for every k ≥ 1 and every k-CNF
φ. -/
def RewritesAtWidthOr3 (pre : List Bool → List Bool) : Prop :=
  ∀ (k n : ℕ) (φ : CNF n), 1 ≤ k → SatK.IsKCNF k φ → pre (SatM.enc k φ) = SatM.enc (widthOr3 φ) φ

/-- The printed test: on the code of (k, φ), k ≥ 1, φ a k-CNF on n variables, `test` is true if and
only if n ≥ K₀^17 and this k, `widthOr3 φ`, is at most (log n)^(1/4). -/
def TestsTheMainRegime (K₀ : ℕ) (test : List Bool → Bool) : Prop :=
  ∀ (k n : ℕ) (φ : CNF n), 1 ≤ k → SatK.IsKCNF k φ → (test (SatM.enc k φ) = true ↔ K₀ ^ 17 ≤ n ∧ ((widthOr3 φ : ℕ) : ℝ) ^ 4 ≤ lg n)

/-- For every K₀ there are a polynomial-time front end and a polynomial-time test of this kind. -/
def FrontEndAndTestExist : Prop :=
  (∃ pre : List Bool → List Bool, PolyT pre ∧ RewritesAtWidthOr3 pre) ∧ ∀ K₀ : ℕ, ∃ test : List Bool → Bool, PolyT test ∧ TestsTheMainRegime K₀ test

/-- «… the algorithm tries all assignments; … this takes time 2^n·n^{O(k)}, reading the input
included.» Mb, started on the code of (k, φ), for k ≥ 1, n ≥ 2 and a k-CNF φ on n variables, puts
out the number of satisfying assignments within 2^{c·n}·n^{c·k} steps. -/
def TriesAllWithin (Mb : TM2ComputableAux Bool Bool) (c : ℕ) : Prop :=
  ∀ (k n : ℕ) (φ : CNF n), 1 ≤ k → 2 ≤ n → SatK.IsKCNF k φ → CountsWithin Mb k φ (2 ^ (c * n) * n ^ (c * k))

/-- On every bit string x the machine M puts out f (x, padding string of 2^(e x) units) within
q·(|x| + 2^(e x) + 1)^q steps. -/
def Computes (M : TM2ComputableAux Bool Bool) (f : List Bool × U → List Bool) (e : List Bool → ℕ) (q : ℕ) : Prop :=
  ∀ x : List Bool, Outputs M x (f (x, PaddedDescent.pad (e x))) (q * (x.length + 2 ^ e x + 1) ^ q)

/-- Exhaustive counting as a function of (input, padding string): how many numbers below 2ⁿ, cut off
at the length of the padding string, code a satisfying assignment of the formula written in the
input (`UniformInK.bruteU`), in n + 1 bits. -/
def exhaust (p : List Bool × U) : List Bool := CountKSat.outW (fmlOf p.1, UniformInK.bruteU p)

/-- EVERY machine that computes exhaustive counting with a padding string of 2ⁿ units tries all
assignments within 2^{c·n}·n^{c·k} steps, for some c. -/
def EveryExhaustiveMachineTriesAll : Prop :=
  ∀ (Mb : TM2ComputableAux Bool Bool) (qb : ℕ), Computes Mb exhaust (fun x => (fmlOf x).1.length) qb → ∃ c : ℕ, TriesAllWithin Mb c

/-- There is such a machine, and it is tied to exhaustive counting: on EVERY bit string x it
computes `exhaust` with a padding string of 2ⁿ units, n the number of variables written in x. -/
def ExhaustiveMachineExists : Prop :=
  ∃ (Mb : TM2ComputableAux Bool Bool) (c q : ℕ), (∀ i, Finite (Mb.tm.Γ i)) ∧ TriesAllWithin Mb c ∧ Computes Mb exhaust (fun x => (fmlOf x).1.length) q

/-- «as there are fewer than (2n+1)^k ≤ n^(2k) clauses»: (2n+1)^k ≤ n^(2k) for n ≥ 3; that a k-CNF
has at most (2n+1)^k clauses is `MainTheoremForms.ClauseCountStmt`. -/
def ClauseCountPowStmt : Prop := ∀ k n : ℕ, 3 ≤ n → (2 * n + 1) ^ k ≤ n ^ (2 * k)

/-! ### Sentence (8) -/

/-- «It is within the bound: log n ≤ n/√(log n) ≤ n·log log n/√(log n) for n ≥ 4, so k·log n ≤
k²·n·log log n/√(log n); if k > (log n)^(1/4), then k²·n·log log n/√(log n) ≥ n·log log n ≥ n; and
if n < K₀^17, then n·log log n/√(log n) ≥ n/√(17·log K₀).» -/
def FallBackIsWithinTheBound : Prop :=
  (∀ n : ℕ, 4 ≤ n → lg n ≤ n / Real.sqrt (lg n) ∧ (n : ℝ) / Real.sqrt (lg n) ≤ n * lg (lg n) / Real.sqrt (lg n)) ∧
  (∀ k n : ℕ, 1 ≤ k → 4 ≤ n → (k : ℝ) * lg n ≤ expN k n) ∧
  (∀ k n : ℕ, 4 ≤ n → lg n < (k : ℝ) ^ 4 → (n : ℝ) * lg (lg n) ≤ expN k n ∧ (n : ℝ) ≤ n * lg (lg n)) ∧
  (∀ K₀ n : ℕ, 2 ≤ K₀ → 4 ≤ n → n < K₀ ^ 17 → (n : ℝ) / Real.sqrt (17 * lg K₀) ≤ n * lg (lg n) / Real.sqrt (lg n))

/-! ### The conclusion of (b) -/

/-- **The main statement.** Let S be a solver with a sequence Q of levels and e_ℓ ≤ a/√(log K_ℓ) for
all ℓ; let M with C′ have the conclusion of Theorem D (a) for S and Q; let Mb with c try all
assignments; let `pre` rewrite the code at k = `widthOr3 φ` and `test` be the printed test with K₀ =
K at the level 0. All of these are arbitrary.
Then EVERY machine N that chooses, by `test`, between M behind `pre` and Mb on the input as it is,
for whatever q, meets the bound of Theorem D (b) with some constant C: for all k ≥ 1, n ≥ 4 and
every k-CNF on n variables, within 2^{C·k²·n·log log n/√(log n)} steps. -/
def EveryChoiceMeetsThmVariablesB : Prop :=
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀) (a : ℕ), (∀ l : ℕ, e l ≤ a / Real.sqrt (lg (S.K (Q.idx l)))) →
    ∀ (M : TM2ComputableAux Bool Bool) (C' : ℕ), ThmVariablesAFor S Q M C' → ∀ (Mb : TM2ComputableAux Bool Bool) (c : ℕ), TriesAllWithin Mb c →
      ∀ (pre : List Bool → List Bool) (test : List Bool → Bool), RewritesAtWidthOr3 pre → TestsTheMainRegime (S.K (Q.idx 0)) test →
        ∀ (N : TM2ComputableAux Bool Bool) (q : ℕ), Chooses M Mb test pre id id id N q → ∃ C : ℕ, ThmVariablesBFor N C

/-- Existence and the main statement in one, under the hypotheses of `EveryChoiceMeetsThmVariablesB`
on S, Q, a, M, C′, with the alphabets of M finite: (1) there are Mb, c, `pre`, `test`, N, q as
there, with `pre` and `test` polynomial-time and the alphabets of Mb and N finite, where Mb computes
the named function `exhaust` and N carries out the named computation
`TwoMachines.choose` on codings of M and Mb; (2) every such N meets the bound of Theorem D (b). -/
def ThmVariablesBFromThmVariablesA : Prop :=
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀) (a : ℕ), (∀ l : ℕ, e l ≤ a / Real.sqrt (lg (S.K (Q.idx l)))) →
    ∀ (M : TM2ComputableAux Bool Bool) (C' : ℕ), (∀ i, Finite (M.tm.Γ i)) → ThmVariablesAFor S Q M C' →
      (∃ (Mb : TM2ComputableAux Bool Bool) (c qb : ℕ) (pre : List Bool → List Bool) (test : List Bool → Bool) (K₁ : Coding M) (K₂ : Coding Mb) (N : TM2ComputableAux Bool Bool) (q₀ q : ℕ),
          (∀ i, Finite (Mb.tm.Γ i)) ∧ TriesAllWithin Mb c ∧ Computes Mb exhaust (fun x => (fmlOf x).1.length) qb ∧
          PolyT pre ∧ RewritesAtWidthOr3 pre ∧ PolyT test ∧ TestsTheMainRegime (S.K (Q.idx 0)) test ∧
          (∀ i, Finite (N.tm.Γ i)) ∧ Hosts (choose K₁ K₂ test pre id id id) N q₀ ∧ Chooses M Mb test pre id id id N q) ∧
        ∀ (Mb : TM2ComputableAux Bool Bool) (c : ℕ), TriesAllWithin Mb c →
          ∀ (pre : List Bool → List Bool) (test : List Bool → Bool), RewritesAtWidthOr3 pre → TestsTheMainRegime (S.K (Q.idx 0)) test →
            ∀ (N : TM2ComputableAux Bool Bool) (q : ℕ), Chooses M Mb test pre id id id N q → ∃ C : ℕ, ThmVariablesBFor N C

/-- If Theorem D (a) holds (`MainTheoremForms.ThmVariablesA`) and Theorem B holds
(`AppRunningTime.ThmHalfPieces`: the functions of Appendix B are pieces with parameters (1/√2, c),
for some c), then Theorem D (b) holds. The route is in `ThePairsSatisfyTheHypothesis`,
`ThetaOfThePairs` and `ThmVariablesBFromThmVariablesA`. -/
def ThmVariablesAImpliesThmVariablesB : Prop := ThmVariablesA → AppRunningTime.ThmHalfPieces → ThmVariablesB

end PairsToBound
