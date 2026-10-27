/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CliqueLevelsStatement
public import CountedToPadded.Defs
public import MainTheoremFormsStatement
public import VariableBound.Printed.ThmVariablesADefs
public import RecursionToBound.Defs

/-! # Theorem D (a), with the hypothesis in counted operations: definitions and statements

**The paper**, Theorem D (a): «For a constant C₀ ≥ 1 and all integers ℓ ≥ 0 let K_ℓ ≥ 2 be integers
and e_ℓ reals with K_ℓ < K_(ℓ+1) ≤ K_ℓ^C₀ and (log K_ℓ)^(−C₀) ≤ e_ℓ ≤ 1. Suppose that K_ℓ and a
number in [e_ℓ, 2e_ℓ] can be computed from ℓ in time polynomial in K_ℓ, and that one deterministic
algorithm, given ℓ ≥ 0, λ, B ≥ 1 and query access to tables with |W_w| < 2^B, outputs the
value of the (K_ℓ, λ)-clique within 2^{e_ℓK_ℓ²λ}·(K_ℓ(λ+B))^{C₀K_ℓ²} operations. Then one
deterministic algorithm computes, for all integers n and k with n ≥ K₀^17 and 3 ≤ k ≤ (log n)^(1/4),
the number of satisfying assignments of a k-CNF on n variables in time 2^{O(k²·e·n·log(k/e))}, where
e = e_ℓ for the largest ℓ with K_ℓ ≤ n^(1/17). In particular, if e_ℓ = O((log K_ℓ)^(−α′)) for a
constant
α′ > 0, the time is 2^{O(k²·n·log log n/(log n)^α′)}.»

**The form with a padding string.** In `MainTheoremForms.ThmVariablesA` and in
`RecursionToBound.ThmVariablesAWithNumberBetween` the algorithm for cliques is a function of
(padding string, index, instance with the tables WRITTEN OUT) that is polynomial-time in all three
and right when the padding string is long enough; display (57) bounds the length of the padding
string.

**What is stated here.** The hypothesis follows the printed one clause by clause (with two
additions, item (1) below), in the definitions of `CliqueLevelsStatement.lean`, which serve Theorem
A (b) as well: sequences K : ℕ → ℕ and e : ℕ → ℝ (`CliqueLevels.Levels`); K_ℓ and a number in [e_ℓ,
2e_ℓ] computed in time polynomial in K_ℓ (`ComputesLevels`, `NumberBetween`); ONE machine E with
query access to the tables, in which a query costs one operation, that outputs the
value of the clique within the number of operations of display (57) (`Solves`).
* `Hypothesis K e C₀ kf num E`: all of it. `Conclusion K e M C`: the bound for the machine M and the
  constant C. `PartA`: the theorem. `InParticular`: its last sentence.
* `PartAForEveryMachine`: `PartA` says «there is a machine» and would read the same whichever way it
  was proved. This statement names the algorithm: the function `RecursionToBound.count` of the
  printed Step 5, on the solver `QueryMachines.Bridge.solverOfMachine E num C₀` that is made from E
  by the step «counted operations → padding string». Some machine computes it, and EVERY machine
  that computes it has the bound. So the
  speed of the machine can only come from E.
* `SolverFromMachine`: what `PartA` alone needs of that step: from every such E a solver in the
  padding-string sense with a sequence of levels for the same K_ℓ and for e′_ℓ = the number in [e_ℓ,
  2e_ℓ], cut at 1. It forgets the name of the solver and how the level is picked.
* `BoundAtANumberBetween`: the bound at a number in [e, 2e] is the bound at e with twice the
  constant.

**What differs from the paper.** (1) An operation is a step of E, that is, any function of the state
that is computed in polynomial time (`PolyTimeSteps`), or a query; and the hypothesis ASKS MORE than
the printed one in that the states of E are bounded by the same number as its operations. At fixed
(e, C₀) the two hypotheses cannot be compared; they agree up to constants that the O of
the conclusion absorbs. (2) The conclusion counts steps of Mathlib's machine, with the conventions
of `MainTheoremFormsStatement.lean`: the width k is declared in the input, formulas are lists, a
formula with an empty clause counts 0. (3) The PROOF renders operations as the length of a padding
string from the first step on: Steps 3 to 5 are not done as counts of operations. (4) C′ is chosen
after E. In this model it
necessarily depends on the polynomials that bound the steps of E, of kf and of num, so «the
constants depend only on those of the hypothesis» has no counterpart. (5) C₀ is a natural number. (6)
ℓ, λ and B are given to E in unary. (7) «K_ℓ … can be computed from ℓ in time polynomial in K_ℓ» is
a polynomial-time function of ℓ and a bound b in unary that returns K_ℓ if K_ℓ ≤ b; the number in
[e_ℓ, 2e_ℓ] is a fraction, computed
from ℓ and K_ℓ in unary. Both are equivalent to the printed clauses. (8) That the pairs of display (40)
satisfy THIS hypothesis (Theorem D (b), first sentence) is not stated here: it needs Theorem A (b)
in counted operations. -/

@[expose] public section

namespace ThmVariables

open Turing Groundwork PaddedDescent.F ClauseBound.Alg QueryMachines QueryMachines.Bridge Printed CliqueLevels MainTheoremForms
open Sat3 (CNF)

/-- «the largest ℓ with K_ℓ ≤ n^(1/17)»: K_ℓ^17 ≤ n < K_(ℓ+1)^17. -/
def IsLevel (K : ℕ → ℕ) (n l : ℕ) : Prop := K l ^ 17 ≤ n ∧ n < K (l + 1) ^ 17

/-- The hypothesis of Theorem D (a), clause by clause; `steps`, and the bound on the sizes of the
states inside `solves`, are additions (item (1) of the head comment). -/
structure Hypothesis (K : ℕ → ℕ) (e : ℕ → ℝ) (C₀ : ℕ) (kf : List Unit × List Unit → Option (List Unit)) (num : List Unit × List Unit → ℕ × ℕ)
    (E : QueryMachine TableQuery ℤ (List Unit × List Unit × List Unit) ℤ) : Prop where
  /-- «let K_ℓ ≥ 2 be integers and e_ℓ reals with K_ℓ < K_(ℓ+1) ≤ K_ℓ^C₀ and (log K_ℓ)^(−C₀) ≤ e_ℓ ≤
  1» -/
  levels : Levels K e C₀
  /-- «K_ℓ … can be computed from ℓ in time polynomial in K_ℓ» -/
  computesK : ComputesLevels K kf
  /-- «… and a number in [e_ℓ, 2e_ℓ]» -/
  number : CliqueLevels.NumberBetween K e num
  /-- E is an algorithm: each of its steps is computed in polynomial time -/
  steps : E.PolyTimeSteps
  /-- «one deterministic algorithm, given ℓ ≥ 0, λ, B ≥ 1 and query access to tables with |W_w| <
  2^B, outputs the value of the (K_ℓ, λ)-clique within 2^{e_ℓK_ℓ²λ}·(K_ℓ(λ+B))^{C₀K_ℓ²} operations» -/
  solves : Solves E K e C₀

/-- The bound of Theorem D (a) for the machine M and the constant C: for all n, ℓ and k such that ℓ
is the largest level with K_ℓ ≤ n^(1/17) (so n ≥ K₀^17) and 3 ≤ k ≤ (log n)^(1/4), and every k-CNF φ
on n variables, M computes the number of satisfying assignments within 2^{C·k²·e·n·log(k/e)} steps,
where e = e_ℓ. -/
def Conclusion (K : ℕ → ℕ) (e : ℕ → ℝ) (M : TM2ComputableAux Bool Bool) (C : ℕ) : Prop :=
  ∀ (k n l : ℕ) (φ : CNF n), IsLevel K n l → 3 ≤ k → (k : ℝ) ^ 4 ≤ MainTheoremForms.lg n → SatK.IsKCNF k φ → CountsWithin M k φ (timeVariablesA C k n (e l))

/-- **Theorem D (a).** Under this hypothesis there are one machine with finite alphabets and one
constant C′ with the bound `Conclusion`. -/
def PartA : Prop :=
  ∀ (K : ℕ → ℕ) (e : ℕ → ℝ) (C₀ : ℕ) (kf : List Unit × List Unit → Option (List Unit)) (num : List Unit × List Unit → ℕ × ℕ) (E : QueryMachine TableQuery ℤ (List Unit × List Unit × List Unit) ℤ),
    Hypothesis K e C₀ kf num E → ∃ (M : TM2ComputableAux Bool Bool) (C' : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ Conclusion K e M C'

/-- Theorem D (a), last sentence. «In particular, if e_ℓ = O((log K_ℓ)^(−α′)) for a constant α′ > 0,
the time is 2^{O(k²·n·log log n/(log n)^α′)}.» For all levels, every α′ > 0 and every natural number
c with e_ℓ ≤ c·(log K_ℓ)^(−α′) for all ℓ, EVERY machine M and every C with the bound `Conclusion`:
there is a C′ such that for all n ≥ K₀^17, all k with 3 ≤ k ≤ (log n)^(1/4) and every k-CNF φ on n
variables the same M takes at most 2^{C′·k²·n·log log n/(log n)^α′} steps. -/
def InParticular : Prop :=
  ∀ (K : ℕ → ℕ) (e : ℕ → ℝ) (C₀ : ℕ), Levels K e C₀ → ∀ (α' : ℝ) (c : ℕ), 0 < α' → (∀ l : ℕ, e l ≤ c / MainTheoremForms.lg (K l) ^ α') →
    ∀ (M : TM2ComputableAux Bool Bool) (C : ℕ), Conclusion K e M C →
      ∃ C' : ℕ, ∀ (k n : ℕ) (φ : CNF n), K 0 ^ 17 ≤ n → 3 ≤ k → (k : ℝ) ^ 4 ≤ MainTheoremForms.lg n → SatK.IsKCNF k φ → CountsWithin M k φ (timeVariablesAAlpha C' k n α')

/-- **Theorem D (a) for every machine that runs the named algorithm.** Under the hypothesis, with
any certificate that E has polynomial-time steps (the solver made from E depends on the coding of
its states, which is data), there is an n₀ such that for every n₁ ≥ n₀ (i) some machine with finite
alphabets computes the algorithm of Step 5, `RecursionToBound.count`, on the solver that E gives
(`QueryMachines.Bridge.solverOfMachine E num C₀`), with the level picked by `pickOf kf (K 0)` and
the number in [e′_ℓ, 2e′_ℓ] computed by `cutFraction num`, with the exponent `RecursionToBound.expo`
of the same; and (ii) EVERY machine that computes this function with this exponent, for whatever q,
has the bound `Conclusion K e` with some constant C′. -/
def PartAForEveryMachine : Prop :=
  ∀ (K : ℕ → ℕ) (e : ℕ → ℝ) (C₀ : ℕ) (kf : List Unit × List Unit → Option (List Unit)) (num : List Unit × List Unit → ℕ × ℕ)
    (E : QueryMachine TableQuery ℤ (List Unit × List Unit × List Unit) ℤ) [QueryMachine.IsPolyQ E], Hypothesis K e C₀ kf num E →
    ∃ n₀ : ℕ, ∀ n₁ : ℕ, n₀ ≤ n₁ →
      (∃ (M : TM2ComputableAux Bool Bool) (q : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧
        PairsToBound.Computes M (RecursionToBound.count (solverOfMachine E num C₀) n₁ (pickOf kf (K 0)) (cutFraction num)) (RecursionToBound.expo (solverOfMachine E num C₀) n₁ (pickOf kf (K 0)) (cutFraction num)) q) ∧
      ∀ (M : TM2ComputableAux Bool Bool) (q : ℕ),
        PairsToBound.Computes M (RecursionToBound.count (solverOfMachine E num C₀) n₁ (pickOf kf (K 0)) (cutFraction num)) (RecursionToBound.expo (solverOfMachine E num C₀) n₁ (pickOf kf (K 0)) (cutFraction num)) q →
          ∃ C' : ℕ, Conclusion K e M C'

/-- It follows from the step from counted operations to the padding string for the named solver
(`QueryMachines.Bridge.SolverOfMachineLevels`) and from Theorem D (a) for every machine that
computes the function of Steps 1 to 5 on a solver with levels
(`RecursionToBound.ThmVariablesAForEveryMachine`). The proof also uses two theorems that are not
premises here: `ThmVariables.boundAtANumberBetween` (its statement is below), and that the number
e′_ℓ is itself
computed (`ThmVariables.numberBetween_cut`). -/
def PartAForEveryMachineFrom : Prop := SolverOfMachineLevels → RecursionToBound.ThmVariablesAForEveryMachine → PartAForEveryMachine

/-- `PartA` follows from it. -/
def PartAFromEveryMachine : Prop := PartAForEveryMachine → PartA

/-- What `PartA` alone needs of the step from counted operations to the padding string: under the
hypothesis there is a polynomial-time solver in the sense of
proof/rates/ClauseBound/Alg/Interfaces.lean with a sequence of levels for the same numbers K_ℓ and
for e′_ℓ = `CliqueLevels.cutNumber K num ℓ`, the number in [e_ℓ, 2e_ℓ] cut at 1, with some constant
C₀′. (e′ and not e, because the exponent of a
padding string must be computed, and the number in [e_ℓ, 2e_ℓ] is the only handle on e_ℓ that can be
computed.) -/
def SolverFromMachine : Prop :=
  ∀ (K : ℕ → ℕ) (e : ℕ → ℝ) (C₀ : ℕ) (kf : List Unit × List Unit → Option (List Unit)) (num : List Unit × List Unit → ℕ × ℕ) (E : QueryMachine TableQuery ℤ (List Unit × List Unit × List Unit) ℤ),
    Hypothesis K e C₀ kf num E → ∃ (Idx : Type) (_ : Enc Idx) (S : Solver Idx) (C₀' : ℕ) (Q : S.Seq (cutNumber K num) C₀'), S.Poly ∧ ∀ l : ℕ, S.K (Q.idx l) = K l

/-- The bound at a number in [e, 2e] is the bound at e with twice the constant: for 0 < e ≤ e′ ≤ 2e,
e′ ≤ 1 and k ≥ 1, 2^{C·k²·e′·n·log(k/e′)} ≤ 2^{2C·k²·e·n·log(k/e)}, both rounded down. -/
def BoundAtANumberBetween : Prop :=
  ∀ (C k n : ℕ) (e e' : ℝ), 1 ≤ k → 0 < e → e ≤ e' → e' ≤ 2 * e → e' ≤ 1 → timeVariablesA C k n e' ≤ timeVariablesA (2 * C) k n e

/-- Theorem D (a) with this hypothesis follows from Theorem D (a) with the padding string
(`RecursionToBound.ThmVariablesAWithNumberBetween`) and the step from a machine to a solver. The
proof also uses two theorems that are not premises here: `ThmVariables.boundAtANumberBetween`, and
that the number e′_ℓ is itself computed (`ThmVariables.numberBetween_cut`). Premises and conclusion
are theorems, so by its statement alone this shows little; the route is in `PartAForEveryMachine`. -/
def PartAFromThePaddingString : Prop := SolverFromMachine → RecursionToBound.ThmVariablesAWithNumberBetween → PartA

end ThmVariables
