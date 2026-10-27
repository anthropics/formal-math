/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsifyThenCount.Defs

/-! # The plan is used: definitions and statements

The function for the bound in n, and likewise `SparsifyThenCount.ADG Θ`, asks its plan
(`VariableBound.planD`): if there is none, it counts exhaustively (`bruteU`); if there is one, it
walks the counting tree and counts every leaf by `VariableBound.countD`, that
is by Steps 1 to 4 of Appendix D. A statement that such a function is an algorithm for given rates
(`Alg`) does not say in so many words that there ever is a plan. It follows when the rate in n tends
to 0: the plan depends only on k, n, the level picked for n and the
precision, not on the clauses (`planD`); on the code of the formula without clauses the merged
function does not take the algorithm for the bound in m, so without a plan the exponent of the pad
is n, and 2^n is not within the bound in n once the
rate is small. This file states that consequence (`PlanUsed`, `StPlanUsed`) and that the rate in n
tends to 0 (`StRateZero`).

**What `PlanUsed` says.** For every fixed width k ≥ 1 there is an n₀ such that for all n ≥ n₀ and
every k-CNF φ on n variables the plan on the code of (k, φ) exists. So on these inputs the branch
for the bound in n does not count
exhaustively: it is the walk through the counting tree, with the leaves counted by `countD`.

**What it does not say.** n₀ depends on k and is not explicit. On a formula in which all variables
occur, which has a clause, and whose exponent for the bound in m is not the larger one, the merged
function runs the algorithm for the
bound in m and not this branch. A formula with an empty clause has the count 0 without a walk. The
counting tree may be a single leaf. `PlanUsed` follows from `Alg` (`StPlanUsed`); it states what
`Alg` already forces. Only
where the merged function does not take the algorithm for the bound in m does `Alg` say that the
walk's value is right. It does not say that inside `countD` the branch with more clauses than n̄,
where Step 2 searches for checks, is ever
taken. -/

@[expose] public section

namespace SparsifyThenCount

open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN UniformInK VariableBound VariableBound.Decide

/-- For every width k ≥ 1 and all large n, the plan exists on the code of (k, φ), for every k-CNF φ
on n variables. -/
def PlanUsed {Idx : Type} [Enc Idx] (S : Solver Idx) (pick : U → U × Idx) (slU : U → U) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ φ : Sat3.CNF n, SatK.IsKCNF k φ → (planD S pick slU (SatM.enc k φ)).isSome = true

/-- If some function A with the exponent function `VariableBound.eBD S pick slU` is an algorithm for
the rates rn and rm, and rn tends to 0, then the plan is used. -/
def StPlanUsed : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (pick : U → U × Idx) (slU : U → U) (rn rm : ℕ → ℝ) (A : List Bool × U → List Bool),
  Alg rn rm A (eBD S pick slU) → Filter.Tendsto rn Filter.atTop (nhds 0) → PlanUsed S pick slU

/-- The rate log₂ log₂(n+4)/√(log₂(n+4)) tends to 0. -/
def StRateZero : Prop := Filter.Tendsto (SatK.rN 1 (1 / 2)) Filter.atTop (nhds 0)

end SparsifyThenCount
