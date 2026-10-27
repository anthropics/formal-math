/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Top.Defs
public import UniformInK.Top.ArithDefs

/-! # Steps 4 and 5, the arithmetic of the exponent: constants and interface statements

The counterpart of proof/sparsification/UniformInK/Top/ArithDefs.lean. Notation as there: K the
number of nodes at the level picked for n, so that K^17 ≤ n < K^(17·C₀); g = 3K⁸; Y the number of
binary digits of K; β a natural number, later
`betaU k s`; b = β + 3, Δ = D = 2^β, W = b²·D·Y (`UniformInK.WofU`). The exponent of the padding
string (the number of operations, written as a string of ones; Appendix E), `needD`, is Lean's form
of display (70) of Step 4, with the profiles, the lists of checks and the walk of Step 5 added. Its
main term is
e·U with U ≤ 140·k·n·(β+1) + 18·K^16. «All these are o(en)» becomes: every other part, multiplied by
K, is at most a number times W·n (`StLowerD`). That number depends on C₀ only, except for the part
(K − 1)·λ, which
display (70) does not have; there it is 19 + 140·k + G. And W ≤ A₁·K·e (`UniformInK.StMasterU`, used
as it is).
What differs from that file: U, P are the bounds `UbD`, `PbD` of Step 3, known through
`Net.StBounds`; the tables have B = `BbD k n` = 14(k+1)n + 1 bits, which enter only under the
logarithm (`StArgD`); the plan has three tests.
`UniformInK.StMasterU` and the constants `aU`, `A1U` do not involve the bounds U, P and B of Step 3,
and are used as they are.
This file has definitions only. The statements `St…` are propositions; one file proves each of them. -/

@[expose] public section

namespace VariableBound

open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F PaddedDescent.F.Mark CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK VariableBound.Net

/-! ### Constants -/

/-- The constant in g·P ≤ G·W·n. -/
def GD (C₀ : ℕ) : ℕ := 842 + 68 * C₀

/-- The sum of the constants of the parts of lower order. -/
def ccD (k C₀ : ℕ) : ℕ := 3 + 3 * GD C₀ + (19 + 140 * k + GD C₀) + GD C₀ + 18 + 1 + C₀ * (85 * C₀ + 16) + 18 * (4 + 17 * C₀) + (10 + 34 * C₀)

/-- The constant of the alternative ⌊log₂ n⌋ < B·k². -/
def BkD (C C₀ : ℕ) : ℕ := 2 * (102 * C₀ * aU C C₀) ^ 2

/-- The constant A of the bound A·k²·n·e·(s+1). -/
def AexpD (C₀ : ℕ) : ℕ := 140 * 35 + (ccD 0 C₀ + 140) * A1U C₀ + 1 + 4

/-! ### Natural numbers, for an arbitrary β -/

/-- Display (68) in closed form, for Δ = 2^β with β ≥ 1 and n ≥ 1: `UbD k K n (2^β)`, the right side
of (68) with the logarithms rounded up, is at most 140·k·n·(β+1) + 18·K^16. This is the printed
«O(kn log Δ) + 2g²» with the
constant 140 (⌈log₂(2Δ)⌉ = β + 1 and 2g² = 18·K^16). -/
def StUbD : Prop := ∀ β k K n : ℕ, 1 ≤ β → 1 ≤ n → UbD k K n (2 ^ β) ≤ 140 * k * n * (β + 1) + 18 * K ^ 16

/-- Step 4, «the numbers L and B' are polynomial in n», for k ≤ β, β + 3 ≤ 2^β ≤ n + 1, 2 ≤ K and
K^17 ≤ n < K^(17·C₀): K·(λ + B') ≤ 2^(5·17·C₀·Y + 16), where λ = `lamS` and B' = `bitsS` are this
formalization's bounds for the label
length and the entry length of the rebalanced instance. They stand for the printed L and B': λ =
⌊(K³ + K·U + g·P)/K³⌋ ≥ L, and B' = 6K⁷·P + (6K⁸ + 36K¹⁵)·B in place of ⌈2gP/K⌉ + g²·B. -/
def StArgD : Prop := ∀ β k K n C₀ : ℕ, k ≤ β → β + 3 ≤ 2 ^ β → 2 ≤ K → K ^ 17 ≤ n → n < K ^ (17 * C₀) → 2 ^ β ≤ n + 1 →
  K * (lamS K (3 * K ^ 8) (UbD k K n (2 ^ β)) (PbD K n (2 ^ β)) + bitsS K (3 * K ^ 8) (PbD K n (2 ^ β)) (BbD k n)) ≤ 2 ^ (5 * (17 * C₀ * K.size) + 16)

/-- Step 4, «all these are o(en)», first half, for 1 ≤ β, k ≤ β, 2 ≤ K and K^17 ≤ n < K^(17·C₀): the
parts of lower order of the exponent, each multiplied by K, are at most a number times W·n. The
number depends on C₀ only, except for
the part (K − 1)·λ, where it is 19 + 140·k + G (G = `GD C₀`); display (70) has no such part. -/
def StLowerD : Prop := ∀ β k K n C₀ : ℕ, 1 ≤ β → k ≤ β → 2 ≤ K → K ^ 17 ≤ n → n < K ^ (17 * C₀) →
  K * (3 * K ^ 8 * K.size) ≤ 3 * (WofU β K * n) ∧
  K * (PbD K n (2 ^ β) * (2 * (3 * K ^ 8) / K + 1)) ≤ 3 * GD C₀ * (WofU β K * n) ∧
  K * ((K - 1) * lamS K (3 * K ^ 8) (UbD k K n (2 ^ β)) (PbD K n (2 ^ β))) ≤ (19 + 140 * k + GD C₀) * (WofU β K * n) ∧
  3 * K ^ 8 * PbD K n (2 ^ β) ≤ GD C₀ * (WofU β K * n) ∧
  K * (18 * K ^ 16) ≤ 18 * (WofU β K * n) ∧
  K * K ^ 2 ≤ WofU β K * n ∧
  K * (C₀ * K ^ 2 * (5 * (17 * C₀ * K.size) + 16)) ≤ C₀ * (85 * C₀ + 16) * (WofU β K * n) ∧
  K * (3 * K ^ 8 * (3 * K ^ 8) * 2 * Nat.size (objMax n (2 ^ β))) ≤ 18 * (4 + 17 * C₀) * (WofU β K * n) ∧
  K * (Nat.size (8 * (10 * n + 1) * (sbMax (2 ^ β) + 1) * (Nat.size (2 ^ β * n) + 2) + 8) + 2 + (β + 5 * k + 10 + (k + 3) * n.size)) ≤ (10 + 34 * C₀) * (WofU β K * n)

/-! ### The exponent -/

/-- Steps 4 and 5: the exponent `needD` of the padding string is at most (140·k·35·k + `ccD k C₀`·A₁ + 1)·n·e·(s+1),
if W ≤ A₁·K·e; for k ≥ 1, 2 ≤ K, K^17 ≤ n < K^(17·C₀), 2^β ≤ n + 1, 0 < e ≤ 1, 2^(−s) ≤ e and a
solver with the bound of display (57). -/
def StNeedD : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (i : Idx) (e : ℝ) (C₀ k n s A₁ : ℕ), 1 ≤ k → 2 ≤ S.K i → S.K i ^ 17 ≤ n → n < S.K i ^ (17 * C₀) →
  2 ^ betaU k s ≤ n + 1 → 0 < e → e ≤ 1 → 1 / (2 : ℝ) ^ s ≤ e → ((WofU (betaU k s) (S.K i) : ℕ) : ℝ) ≤ (A₁ : ℝ) * (S.K i) * e →
  (∀ lam B : ℕ, 1 ≤ lam → 1 ≤ B → (S.need (i, List.replicate lam (), List.replicate B ()) : ℝ) ≤
    e * (S.K i : ℝ) ^ 2 * lam + C₀ * (S.K i : ℝ) ^ 2 * Real.logb 2 (S.K i * (lam + B))) →
  (needD S k i n s : ℝ) ≤ ((140 * k * (35 * k) + ccD k C₀ * A₁ + 1 : ℕ) : ℝ) * n * e * ((s : ℝ) + 1)

/-- The exponent of a plan, or else n, is at most `needD` if the three tests are passed and the
solver is polynomial-time. -/
def StPlanNeedD : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx), S.Poly → ∀ (k n : ℕ) (i : Idx) (s : ℕ),
  s0U k ≤ s → 2 ^ betaU k s ≤ n + 1 → 29 * LD (2 ^ betaU k s) + 19 ≤ n → (planAtD S k n i s).getD n ≤ needD S k i n s

end VariableBound
