/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PrintedStatement

/-! # «One deterministic algorithm, given ℓ ≥ 0, λ, B ≥ 1 and query access to tables with |W_w| < 2^B, outputs the value of the (K_ℓ, λ)-clique within 2^{e_ℓK_ℓ²λ}·(K_ℓ(λ+B))^{C₀K_ℓ²} operations»

This sentence stands twice in the paper: as Theorem A (b), a conclusion, and in Theorem D (a), a
hypothesis. Here it is written once, with two bounds on memory: `Solves`, the weaker form, is the
hypothesis of Theorem D (a), and Theorem A (b) is proved in that form too, so that the one can be
fed into the other; `SolvesInFactor`, the sharper form, is the one that says what the sentence says
as a conclusion. The rest of the hypothesis of Theorem D (a) stands beside it, in the printed words,
on sequences K : ℕ → ℕ and e : ℕ → ℝ (`Levels`, `ComputesLevels`, `NumberBetween`). Definitions
only. Imports `PrintedStatement.lean` (query access to the tables of a clique; through it machines
with query access, and what an operation is).

* The algorithm is a machine M with query access to the tables; its input is (ℓ, λ, B) in unary.
  That it has polynomial-time steps is said beside this definition (`M.PolyTimeSteps`), not in it.
* A table query costs one operation (`QueryMachine.unitCost`), as in Definition 3.
* A bound on memory is ADDED to the printed sentence, which has none: the sizes of all states are
  bounded by the same number as the operations. (On a word RAM, T operations touch at most T words;
  in this model a step may rewrite the whole state, so the bound has to be said.) By
  `CountKSat.exists_tmW` the number of steps of a
  Turing machine is then at most a fixed power of the printed bound, which is enough for Theorem D
  (a), whose conclusion has an O in the exponent. So as a hypothesis of Theorem D (a) this
  definition asks more than the printed sentence, which bounds no memory; among the bounds on memory
  it is a weak one, so Theorem D (a) proved from it holds for every sharper one as well. As a
  CONCLUSION it is weaker than the printed sentence reads: T operations on states as
  large as T may stand for a fixed power of T, so the exponent e_ℓK_ℓ²λ is claimed only up to a
  constant factor, fixed with the machine. (It still says something, because ONE machine serves all
  ℓ and e_ℓ → 0.) The form for a conclusion is `SolvesInFactor`.
* C₀ is a natural number; the paper's constant C₀ ≥ 1 may be real, and may be rounded up. Theorem A (b)
  is also proved in a sharper form, with the pieces as an oracle, where the states are bounded by
  the factor (K_ℓ(λ+B))^{C₀K_ℓ²} alone. -/

@[expose] public section

namespace CliqueLevels

open Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines Printed

/-- The printed bound 2^{eK²λ}·(K(λ+B))^{C₀K²}, as a real number. -/
noncomputable def bound (e : ℝ) (K C₀ lam B : ℕ) : ℝ := (2 : ℝ) ^ (e * (K : ℝ) ^ 2 * lam) * ((K : ℝ) * ((lam : ℝ) + B)) ^ (C₀ * K ^ 2)

/-- M, given ℓ ≥ 0, λ, B ≥ 1 and query access to tables with |W_w| < 2^B, outputs the value of the
(K_ℓ, λ)-clique within 2^{e_ℓK_ℓ²λ}·(K_ℓ(λ+B))^{C₀K_ℓ²} operations, on states of at most that size. -/
def Solves (M : QueryMachine TableQuery ℤ (List Unit × List Unit × List Unit) ℤ) (K : ℕ → ℕ) (e : ℕ → ℝ) (C₀ : ℕ) : Prop :=
  ∀ (l lam B : ℕ) (W : ℕ → List Bool → ℤ), 1 ≤ lam → 1 ≤ B → (∀ w < K l, ∀ z ∈ words ((K l - 1) * lam), |W w z| < 2 ^ B) →
    ∃ T S : ℕ, M.Within (tables (K l) lam W) QueryMachine.unitCost (unary l, unary lam, unary B) T S (clique (K l) lam fun w => W w.val).value ∧
      (T : ℝ) ≤ bound (e l) (K l) C₀ lam B ∧ (S : ℝ) ≤ bound (e l) (K l) C₀ lam B

/-- The second factor of the printed bound, (K(λ+B))^{C₀K²}, as a real number. -/
noncomputable def factor (K C₀ lam B : ℕ) : ℝ := ((K : ℝ) * ((lam : ℝ) + B)) ^ (C₀ * K ^ 2)

/-- The same sentence with the sharper bound on memory: all states have size at most the polynomial
factor (K_ℓ(λ+B))^{C₀K_ℓ²} of the printed bound. Then T operations stand for at most T times a fixed
power of that factor in steps of a Turing machine, which is the printed bound with a larger constant
C₀ and THE SAME exponent
e_ℓK_ℓ²λ. This is the form that says what the printed sentence says as a CONCLUSION. (The rule for
conclusions: where a bound on operations is 2^{exponent}·F with F the printed polynomial factor, all
states have size at most F. So it is in Definition 4 and Lemma 1, `PrintedStatement.lean`.) -/
def SolvesInFactor (M : QueryMachine TableQuery ℤ (List Unit × List Unit × List Unit) ℤ) (K : ℕ → ℕ) (e : ℕ → ℝ) (C₀ : ℕ) : Prop :=
  ∀ (l lam B : ℕ) (W : ℕ → List Bool → ℤ), 1 ≤ lam → 1 ≤ B → (∀ w < K l, ∀ z ∈ words ((K l - 1) * lam), |W w z| < 2 ^ B) →
    ∃ T S : ℕ, M.Within (tables (K l) lam W) QueryMachine.unitCost (unary l, unary lam, unary B) T S (clique (K l) lam fun w => W w.val).value ∧
      (T : ℝ) ≤ bound (e l) (K l) C₀ lam B ∧ (S : ℝ) ≤ factor (K l) C₀ lam B

/-- The sharper form gives the weaker one (for e ≥ 0). -/
def SolvesOfSolvesInFactor : Prop := ∀ (M : QueryMachine TableQuery ℤ (List Unit × List Unit × List Unit) ℤ) (K : ℕ → ℕ) (e : ℕ → ℝ) (C₀ : ℕ), (∀ l, 0 ≤ e l) → SolvesInFactor M K e C₀ → Solves M K e C₀

/-- «For a constant C₀ ≥ 1 and all integers ℓ ≥ 0 let K_ℓ ≥ 2 be integers and e_ℓ reals with K_ℓ <
K_(ℓ+1) ≤ K_ℓ^C₀ and (log K_ℓ)^(−C₀) ≤ e_ℓ ≤ 1.» -/
structure Levels (K : ℕ → ℕ) (e : ℕ → ℝ) (C₀ : ℕ) : Prop where
  C₀_pos : 1 ≤ C₀
  K_two : ∀ l, 2 ≤ K l
  K_lt : ∀ l, K l < K (l + 1)
  K_le : ∀ l, K (l + 1) ≤ K l ^ C₀
  e_ge : ∀ l, 1 / Real.logb 2 (K l) ^ C₀ ≤ e l
  e_le : ∀ l, e l ≤ 1

/-- «K_ℓ … can be computed from ℓ in time polynomial in K_ℓ.» K_ℓ may be far longer than ℓ, so this
is not polynomial time in the length of ℓ. The function kf gets ℓ and a bound b, both in unary, is
polynomial-time, and returns K_ℓ in unary if K_ℓ ≤ b, and nothing otherwise. (From an algorithm that
takes time polynomial in
K_ℓ such a function is had by running it for a number of steps polynomial in b; from such a function
K_ℓ is had in time polynomial in K_ℓ by doubling b.) -/
def ComputesLevels (K : ℕ → ℕ) (kf : List Unit × List Unit → Option (List Unit)) : Prop :=
  PolyT kf ∧ ∀ l b : ℕ, kf (unary l, unary b) = if K l ≤ b then some (unary (K l)) else none

/-- «… and a number in [e_ℓ, 2e_ℓ] can be computed from ℓ in time polynomial in K_ℓ.» The function
`num` gets ℓ and K_ℓ in unary, is polynomial-time, and returns the numerator and the denominator of
such a number. -/
def NumberBetween (K : ℕ → ℕ) (e : ℕ → ℝ) (num : List Unit × List Unit → ℕ × ℕ) : Prop :=
  PolyT num ∧ ∀ l : ℕ, e l ≤ ((num (unary l, unary (K l))).1 : ℝ) / ((num (unary l, unary (K l))).2 : ℝ) ∧ ((num (unary l, unary (K l))).1 : ℝ) / ((num (unary l, unary (K l))).2 : ℝ) ≤ 2 * e l

/-- The number that `num` returns for ℓ, cut at 1: as e_ℓ ≤ 1 it is again in [e_ℓ, 2e_ℓ]. -/
noncomputable def cutNumber (K : ℕ → ℕ) (num : List Unit × List Unit → ℕ × ℕ) (l : ℕ) : ℝ := min (((num (unary l, unary (K l))).1 : ℝ) / ((num (unary l, unary (K l))).2 : ℝ)) 1

end CliqueLevels
