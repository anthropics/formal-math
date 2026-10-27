/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import MainTheoremFormsStatement
public import ClauseBound.Alg.Interfaces
public import VariableBound.Params.Defs

/-! # Theorem D (a), its «In particular», and the sentence on n₀: the statements

Definitions only. The file imports proof/rates/ClauseBound/Alg/Interfaces.lean, because the
hypothesis of Theorem D (a) is an algorithm for cliques, and Lean's form of that is the structure
`ClauseBound.Alg.Solver` defined there.

## How the hypothesis of Theorem D (a) is written

* «For a constant C₀ ≥ 1 and all integers ℓ ≥ 0 let K_ℓ ≥ 2 be integers and e_ℓ reals with K_ℓ <
  K_(ℓ+1) ≤ K_ℓ^C₀ and (log K_ℓ)^(−C₀) ≤ e_ℓ ≤ 1»: the fields `K_two`, `K_lt`, `K_le`, `e_ge`,
  `e_le` of `Q : S.Seq e C₀`,
  with K_ℓ = `S.K (Q.idx ℓ)` and e_ℓ = `e ℓ`. C₀ ≥ 1 follows from K_ℓ < K_(ℓ+1) ≤ K_ℓ^C₀.
* «one deterministic algorithm … outputs the value of the (K_ℓ, λ)-clique within 2^(e_ℓ K_ℓ²
  λ)·(K_ℓ(λ+B))^(C₀ K_ℓ²) operations»: the solver S is a polynomial-time function of (pad, index,
  instance) (`S.Poly`) that is right
  whenever the pad has length at least 2^need (`Q.correct`), and need ≤ e_ℓ K_ℓ² λ + C₀ K_ℓ²
  log₂(K_ℓ(λ+B)) (`Q.rate`). So «operations» are replaced by: polynomial time in a pad of that
  length. This assumes less than the
  paper, which bounds the operations by 2^need.
* «K_ℓ … can be computed from ℓ in time polynomial in K_ℓ»: `S.Poly.K`, and `Q.pick`, which finds
  the largest ℓ with K_ℓ at most a bound given in unary (ℓ = 0 if there is none).
* «a number in [e_ℓ, 2e_ℓ] can be computed from ℓ»: `Precision e slU C`. A polynomial-time function
  gives, from ℓ in unary, a number s in unary with 2^(−s) ≤ e_ℓ and 2^s ≤ (2/e_ℓ)^C. For C = 1 this
  says that
  2·2^(−s) is in [e_ℓ, 2e_ℓ].

## What differs from the paper

* The number s must be computed in time polynomial in ℓ; the paper allows time polynomial in K_ℓ.
  Here Lean assumes more than the paper. Its precision is looser: a number in [e_ℓ, 2e_ℓ] gives s
  with C = 2.
* The tables of an instance given to the solver have |W| ≤ 2^B; the paper has |W| < 2^B.
* C₀ is a natural number; the paper allows a real C₀ ≥ 1. Nothing is lost: a real C₀ can be replaced
  by ⌈C₀⌉, because every condition on C₀ gets weaker as C₀ grows (K_ℓ ≥ 2 and log(K_ℓ(λ+B)) ≥ 1).
* The solver must also compute its exponent need in polynomial time, under a bound given in unary
  (the fields `needC`, `needC_eq` and `needC_some` of `S.Poly`); the paper asks nothing of the kind.
  Here Lean assumes more than the paper.
* The solver must be right for every B ≥ 0 (`Solver.Correct` has no condition on B); the paper asks
  this only for B ≥ 1. Here Lean assumes more than the paper.
* The constant C′ of the conclusion comes after the solver, the sequence and the precision function
  with its constant C, and before k, n and the formula. So it does not depend on k; Lean does not
  say that it depends only on C₀ and the
  other constants of the hypothesis.
* `ThmVariablesA` says that SOME machine exists; it does not name the algorithm.
* Machine, input, output and k-CNF are as in `MainTheoremFormsStatement.lean`
  (`MainTheoremForms.CountsWithin`); k is the width written in the input. -/

@[expose] public section

namespace MainTheoremForms

open Turing Groundwork PaddedDescent.F ClauseBound.Alg
open Sat3 (CNF)

/-- From ℓ in unary, `slU` computes in polynomial time a number s in unary with 2^(−s) ≤ e_ℓ and 2^s
≤ (2/e_ℓ)^C. -/
def Precision (e : ℕ → ℝ) (slU : U → U) (C : ℕ) : Prop :=
  PolyT slU ∧ (∀ l : ℕ, 1 / (2 : ℝ) ^ (slU (List.replicate l ())).length ≤ e l) ∧ ∀ l : ℕ, (2 : ℝ) ^ (slU (List.replicate l ())).length ≤ (2 / e l) ^ C

/-- The exponent of Theorem D (a), as printed: k²·e·n·log(k/e). -/
noncomputable def expVariablesA (k n : ℕ) (e : ℝ) : ℝ := (k : ℝ) ^ 2 * e * n * lg (k / e)

/-- The time of Theorem D (a), rounded down: 2^{C·k²·e·n·log(k/e)}. -/
noncomputable def timeVariablesA (C k n : ℕ) (e : ℝ) : ℕ := ⌊(2 : ℝ) ^ ((C : ℝ) * expVariablesA k n e)⌋₊

/-- The time of the «In particular» of Theorem D (a), rounded down: 2^{C·k²·n·log log n/(log n)^α′}. -/
noncomputable def timeVariablesAAlpha (C k n : ℕ) (α' : ℝ) : ℕ := ⌊(2 : ℝ) ^ ((C : ℝ) * ((k : ℝ) ^ 2 * n * lg (lg n) / lg n ^ α'))⌋₊

section
variable {Idx : Type} [Enc Idx] (S : Solver Idx) {e : ℕ → ℝ} {C₀ : ℕ} (Q : S.Seq e C₀)

/-- «The largest ℓ with K_ℓ ≤ n^(1/17)»: K_ℓ^17 ≤ n < K_(ℓ+1)^17. -/
def IsLevel (n l : ℕ) : Prop := S.K (Q.idx l) ^ 17 ≤ n ∧ n < S.K (Q.idx (l + 1)) ^ 17

/-- The bound of Theorem D (a) for the machine M and the constant C: for all n, ℓ and k such that ℓ
is the largest level with K_ℓ ≤ n^(1/17) (so n ≥ K₀^17) and 3 ≤ k ≤ (log n)^(1/4), and every k-CNF φ
on n variables, M computes
the number of satisfying assignments within 2^{C·k²·e·n·log(k/e)} steps, where e = e_ℓ. -/
def ThmVariablesAFor (M : TM2ComputableAux Bool Bool) (C : ℕ) : Prop :=
  ∀ (k n l : ℕ) (φ : CNF n), IsLevel S Q n l → 3 ≤ k → (k : ℝ) ^ 4 ≤ lg n → SatK.IsKCNF k φ → CountsWithin M k φ (timeVariablesA C k n (e l))

end

/-- Theorem D (a). «… Then one deterministic algorithm computes, for all integers n and k with n ≥
K₀^17 and 3 ≤ k ≤ (log n)^(1/4), the number of satisfying assignments of a k-CNF on n variables in
time
2^{O(k² e n log(k/e))}, where e = e_ℓ for the largest ℓ with K_ℓ ≤ n^(1/17).» For every
polynomial-time solver S for cliques with a sequence Q of levels and a precision function slU with
constant C, there are one machine with
finite alphabets and one constant C′ with the bound `ThmVariablesAFor`. -/
def ThmVariablesA : Prop :=
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ (slU : U → U) (C : ℕ), Precision e slU C →
    ∃ (M : TM2ComputableAux Bool Bool) (C' : ℕ), (∀ i, Finite (M.tm.Γ i)) ∧ ThmVariablesAFor S Q M C'

/-- Theorem D (a), last sentence. «In particular, if e_ℓ = O((log K_ℓ)^(−α′)) for a constant α′ > 0,
the time is 2^{O(k² n log log n/(log n)^α′)}.» For every α′ > 0, every natural number c, every
sequence Q of levels with
e_ℓ ≤ c·(log K_ℓ)^(−α′) for all ℓ, every machine M and every C with the bound `ThmVariablesAFor`,
there is a C′ such that for all n ≥ K₀^17, all k with 3 ≤ k ≤ (log n)^(1/4) and every k-CNF φ on n
variables the same M takes at most 2^{C'·k²·n·log log n/(log n)^α′} steps. -/
def ThmVariablesAInParticular : Prop :=
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀) (α' : ℝ) (c : ℕ), 0 < α' → (∀ l : ℕ, e l ≤ c / lg (S.K (Q.idx l)) ^ α') →
    ∀ (M : TM2ComputableAux Bool Bool) (C : ℕ), ThmVariablesAFor S Q M C →
      ∃ C' : ℕ, ∀ (k n : ℕ) (φ : CNF n), S.K (Q.idx 0) ^ 17 ≤ n → 3 ≤ k → (k : ℝ) ^ 4 ≤ lg n → SatK.IsKCNF k φ → CountsWithin M k φ (timeVariablesAAlpha C' k n α')

/-- Step 5, the two facts behind the «In particular». «… because log K > (log n)/(17C₀), and
log(k/e) ≤ (C₀ + 1/4)·log log n.» For the level ℓ of n, K = K_ℓ, e = e_ℓ, and 1 ≤ k ≤ (log n)^(1/4). -/
def StepSparsifyFactsStmt : Prop :=
  ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀) (k n l : ℕ), IsLevel S Q n l → 1 ≤ k → (k : ℝ) ^ 4 ≤ lg n →
    lg n / (17 * C₀) < lg (S.K (Q.idx l)) ∧ lg (k / e l) ≤ (C₀ + 1 / 4) * lg (lg n)

/-- Step 5. «… because k log n ≤ en for large n. Here n is large if it exceeds a bound that depends
only on the constants of the hypothesis.» For every C₀ there is an n₁ such that k·log n ≤ e·n for
all n ≥ n₁, all k ≤ (log n)^(1/4)
and all real e ≥ (log n)^(−C₀). -/
def StepSparsifyLargeStmt : Prop :=
  ∀ C₀ : ℕ, ∃ n₁ : ℕ, ∀ (k n : ℕ) (e : ℝ), n₁ ≤ n → (k : ℝ) ^ 4 ≤ lg n → 1 / lg n ^ C₀ ≤ e → (k : ℝ) * lg n ≤ e * n

/-- Step 5. «For the finitely many smaller n ≥ K₀^17, and the k ≤ (log n)^(1/4) that go with them,
trying all assignments is within the bound.» Trying all assignments takes time 2^n·n^{O(k)}. For
every C₀ and n₁ there is a c such that n ≤ c·k²·e·n·log(k/e) and
k·log n ≤ c·k²·e·n·log(k/e) for all n with 2 ≤ n < n₁, all k ≥ 3 and all real e with (log n)^(−C₀) ≤
e ≤ 1. -/
def StepSparsifySmallStmt : Prop :=
  ∀ C₀ n₁ : ℕ, ∃ c : ℕ, ∀ (k n : ℕ) (e : ℝ), 2 ≤ n → n < n₁ → 3 ≤ k → 1 / lg n ^ C₀ ≤ e → e ≤ 1 → (n : ℝ) ≤ c * expVariablesA k n e ∧ (k : ℝ) * lg n ≤ c * expVariablesA k n e

/-- «Setting and parameters», the sentence on n₀. «As log Δ ≤ 4kC₀ log log n ≤ 4C₀ (log n)^(1/4) log
log n, there is an n₀ that depends only on C₀ such that for n ≥ n₀ … Δ ≤ n^(1/(40C₀)), n ≥ 2 log(2Δ)
and r̄ ≤ 10n, M ≤ 14n.»
For every C₀ ≥ 1 there is an n₀ such that for all n ≥ n₀, all k ≤ (log n)^(1/4) and all Δ with 2 ≤ Δ
≤ (log n)^(4kC₀): the two inequalities for log Δ, the two for Δ and n, and r̄ ≤ 10n, M ≤ 14n for
every m with n̄ < m ≤ Δn, where n̄ and
r̄ are the parameters of the text (`AppVariables.IsNb`, `AppVariables.IsRb`), β =
`AppVariables.beta` and M = `AppVariables.Mb`. -/
def SettingN0Stmt : Prop :=
  ∀ C₀ : ℕ, 1 ≤ C₀ → ∃ n₀ : ℕ, ∀ n k Δ : ℕ, n₀ ≤ n → (k : ℝ) ^ 4 ≤ lg n → 2 ≤ Δ → (Δ : ℝ) ≤ lg n ^ (4 * k * C₀) →
    lg Δ ≤ 4 * k * C₀ * lg (lg n) ∧ 4 * (k : ℝ) * C₀ * lg (lg n) ≤ 4 * C₀ * lg n ^ (1 / 4 : ℝ) * lg (lg n) ∧
    (Δ : ℝ) ≤ (n : ℝ) ^ (1 / (40 * C₀ : ℝ)) ∧ 2 * lg (2 * Δ) ≤ n ∧
    ∀ m nb rb : ℕ, nb < m → m ≤ Δ * n → AppVariables.IsNb n Δ nb → AppVariables.IsRb (AppVariables.beta n m nb) rb → rb ≤ 10 * n ∧ AppVariables.Mb (AppVariables.beta n m nb) rb ≤ 14 * n

end MainTheoremForms
