/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Count.Defs
public import UniformInK.Top.Defs

/-! # The exponent for all widths k, with the count of a sparse formula as in the printed Steps 1 to 4: definitions and interface statements

The twin of proof/sparsification/UniformInK/Top/Defs.lean. The input (1ᵏ 0 1ⁿ 0 and the clauses),
the level picked for n, the precision s, the sparsification with the thresholds `thetaU τ`, τ =
2^(4s+17), the walk through the counting tree, the number
Δ = 2^β with β = `betaU k s`, the cut-off of the width inside the walk, exhaustive counting, and the
merge with the algorithm for the bound in m are those of that file, and its definitions are used.
What differs:
* a leaf of the counting tree is counted by `countD` (Steps 1 to 4 of Appendix D as printed) in
  place of `countOL`;
* the plan has three tests in place of five: s ≥ `s0U k`; 2^β ≤ n + 1; n ≥ 29·⌈log₂(2Δ)⌉ + 19, which
  gives the bounds r̄ ≤ 10n and M ≤ 14n of the Setting of Appendix D. There is no parameter a.
The text assumes 3 ≤ k ≤ (log n)^(1/4) and n ≥ n₀ and falls back on exhaustive counting otherwise
(Step 6). A program must compute its tests, so these three take that place.
This file has definitions only. The statements `St…` are propositions; one file proves each of them. -/

@[expose] public section

namespace VariableBound

open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F PaddedDescent.F.Mark CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK VariableBound.Net

section
variable {Idx : Type} [Enc Idx] (S : Solver Idx)

/-! ### The functions -/

/-- The count of the formula of a node of the counting tree. Δ = 2^β, cut off at n + 1. -/
def valD (k : ℕ) (pad : U) (i : Idx) (n s : ℕ) (x : CNode) : ℕ := countD S k pad i n (blockU k n s) (leafM x)

/-- The exponent of a pad that suffices for everything but the networks: the list of profiles, the
list of checks, the rounds of the walk, the stack of the walk. -/
def restD (k K n s : ℕ) : ℕ :=
  3 * K ^ 8 * (3 * K ^ 8) * 2 * Nat.size (objMax n (blockU k n s)) +
    Nat.size (8 * (10 * n + 1) * (sbMax (blockU k n s) + 1) * (Nat.size (blockU k n s * n) + 2) + 8) + (n / 2 ^ s + 2) +
    (betaU k s + 5 * k + 10 + (k + 3) * Nat.size n)

/-- The exponent of a pad that suffices for n variables at the index i with precision s. -/
def needD (k : ℕ) (i : Idx) (n s : ℕ) : ℕ :=
  needNet S i (UbD k (S.K i) n (blockU k n s)) (PbD (S.K i) n (blockU k n s)) (BbD k n) + restD k (S.K i) n s

/-- If s ≥ s0U k, 2^β ≤ n + 1 and n ≥ 29·⌈log₂(2·2^β)⌉ + 19 (β = betaU k s), and the exponent of the
networks, computed under the bound n, exists and plus `restD` is at most n: that sum (which is
`needD` for a polynomial-time solver,
`Correct.planAtD_some`). Otherwise `none`, and exhaustive counting is used. -/
def planAtD (k n : ℕ) (i : Idx) (s : ℕ) : Option ℕ :=
  if s0U k ≤ s ∧ 2 ^ betaU k s ≤ n + 1 ∧ 29 * LD (2 ^ betaU k s) + 19 ≤ n then
    (needNetC S (List.replicate n ()) i (UbD k (S.K i) n (blockU k n s)) (PbD (S.K i) n (blockU k n s)) (BbD k n)).bind fun v =>
      if v + restD k (S.K i) n s ≤ n then some (v + restD k (S.K i) n s) else none
  else none

/-- The plan for the input x. -/
def planD (pick : U → U × Idx) (slU : U → U) (x : List Bool) : Option ℕ :=
  planAtD S (kU x) (nU x) (idxU pick x) (precU pick slU x)

/-- The exponent function for the bound in n: the exponent of the plan, or n. -/
def eD (pick : U → U × Idx) (slU : U → U) (x : List Bool) : ℕ := (planD S pick slU x).getD (nU x)

/-! ### The choice between the two algorithms by an «if» (proof of Corollary 11: «computing the two exponents … and running only the algorithm with the smaller one»; here the two exponents are computed exactly) -/

/-- Is the algorithm for the bound in m taken? Only if every variable occurs, there is a clause, and
its exponent is not the larger one. -/
def useMD (pick : U → U × Idx) (slU : U → U) (x : List Bool) : Bool :=
  allOccU x && decide (1 ≤ (fmlOf x).2.length) && decide (eM S pick x ≤ eD S pick slU x)

/-- The exponent function of the choice: that for the bound in m where `useMD` holds, that for the
bound in n elsewhere. -/
def eBD (pick : U → U × Idx) (slU : U → U) (x : List Bool) : ℕ :=
  bif useMD S pick slU x then eM S pick x else eD S pick slU x

end

/-! ### The budgets -/

/-- The budgets other than those of the networks, for k ≥ 1 and s ≥ s0U k: a pad of length at least
2^(restD …) suffices for the list of profiles, the list of checks, the rounds of the walk and its
stack. -/
def StBudgetD : Prop := ∀ k K n s F : ℕ, 1 ≤ k → s0U k ≤ s → 2 ^ restD k K n s ≤ F →
  nPrMax K n (blockU k n s) ≤ F ∧
  8 * (10 * n + 1) * (sbMax (blockU k n s) + 1) * (Nat.size (blockU k n s * n) + 2) + 8 ≤ F ∧
  2 * (∑ j ∈ Finset.range (k * n / tauOf s + 1), (bsumU (tauOf s) k * n).choose j) ≤ F + 1 ∧ stackLenCU k (tauOf s) n (inLen k n) ≤ F

/-! ### The exponents -/

/-- For k ≥ 1 and a k-CNF: the exponent is at most that of the algorithm for n, and, if all
variables occur and there is a clause, at most that of the algorithm for m. -/
def StExpBD : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (k : ℕ) (pick : U → U × Idx) (slU : U → U) (n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → SatK.IsKCNF k φ →
  eBD S pick slU (SatM.enc k φ) ≤ eD S pick slU (SatM.enc k φ) ∧
  (SatM.AllOccur φ → 1 ≤ φ.length → eBD S pick slU (SatM.enc k φ) ≤ eM S pick (SatM.enc k φ))

/-! ### Steps 4 and 5: the exponent is O(k²·e·n·(s+1)), with an absolute constant, unless k² is larger than a multiple of log n

The text has 2^O(k²·e·n·log(k/e)) for 3 ≤ k ≤ (log n)^(1/4); here s+1 takes the place of log(k/e)
(the plan asks s ≥ 2·(bit length of k), and s ≥ log₂(1/e)), and the alternative ⌊log₂ n⌋ < B·k²
takes the place of the range of k. -/

/-- The exponent of a plan, or else n, is at most n. -/
def StPlanLeD : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (k n : ℕ) (i : Idx) (s : ℕ), (planAtD S k n i s).getD n ≤ n

/-- For a polynomial-time solver S with a sequence of levels Q, and a precision s(l) (the length of
slU l) with 1/2^s(l) ≤ e_l and 2^s(l) ≤ (2/e_l)^C for every l: there are A and B, depending on
neither k nor n, such that for k ≥ 1 and
n ≥ K₀^17 (K₀ the number of nodes of the clique of level 0), with l the level picked for n and s =
s(l), the exponent of the plan, or n if there is none, is at most A·k²·n·e_l·(s+1), or ⌊log₂ n⌋ <
B·k². -/
def StArithD : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ (slU : U → U) (C : ℕ),
  (∀ l : ℕ, 1 / (2 : ℝ) ^ (slU (List.replicate l ())).length ≤ e l) → (∀ l : ℕ, (2 : ℝ) ^ (slU (List.replicate l ())).length ≤ (2 / e l) ^ C) →
  ∃ A B : ℕ, ∀ k n : ℕ, 1 ≤ k → S.K (Q.idx 0) ^ 17 ≤ n →
    ((planAtD S k n (Q.pick (root17 n)).2 (slU (Q.pick (root17 n)).1).length).getD n : ℝ) ≤
      A * (k : ℝ) ^ 2 * n * e (Q.pick (root17 n)).1.length * ((slU (Q.pick (root17 n)).1).length + 1 : ℝ) ∨ Nat.log 2 n < B * k ^ 2

/-! ### Step 6: the running time of the padding machine against the bound in n -/

/-- For the exponent of the algorithm for n: q·(|x| + 2^e + 1)^q is within the bound in n with k² in
the exponent, for every q, with a constant D that does not depend on k; for k ≥ 1, n ≥ 1 and every
k-CNF. -/
def StTimeD : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (e : ℕ → ℝ) (C₀ : ℕ) (Q : S.Seq e C₀), S.Poly → ∀ (slU : U → U) (C : ℕ),
  (∀ l : ℕ, 1 / (2 : ℝ) ^ (slU (List.replicate l ())).length ≤ e l) → (∀ l : ℕ, (2 : ℝ) ^ (slU (List.replicate l ())).length ≤ (2 / e l) ^ C) →
  ∀ (r : ℕ → ℝ) (c₁ : ℕ), (∀ n : ℕ, 1 ≤ n → 1 / (c₁ * Real.logb 2 ((n : ℝ) + 2) ^ c₁) ≤ r n) →
  (∀ n : ℕ, S.K (Q.idx 0) ^ 17 ≤ n → e (Q.pick (root17 n)).1.length * ((slU (Q.pick (root17 n)).1).length + 1 : ℝ) ≤ c₁ * r n) → FallBack r →
  ∀ q : ℕ, ∃ D : ℕ, ∀ (k n : ℕ) (φ : Sat3.CNF n), 1 ≤ k → 1 ≤ n → SatK.IsKCNF k φ →
    q * ((SatM.enc k φ).length + 2 ^ eD S Q.pick slU (SatM.enc k φ) + 1) ^ q ≤ SatM.boundNK r D k n

end VariableBound
