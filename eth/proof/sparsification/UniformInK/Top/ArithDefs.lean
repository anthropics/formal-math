/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import UniformInK.Top.Defs

/-! # The arithmetic of the exponent: constants and interface statements

Notation: K the number of nodes at the level picked for n, so that K^17 ≤ n < K^(17·C₀); Y the
number of binary digits of K; β a natural number, later `betaU k s`; b = β + 3, D = 2^β,
W = b²·D·Y (`WofU`). The plan is that of proof/rates/ClauseBound/ParityChecks/ArithOL.lean. What
differs: the inequality W ≤ A₁·K·e has a constant A₁ that depends on C₀ only, under the hypothesis
D⁶ ≤ K;
and D⁶ ≤ K follows from 2·(102·C₀·c)² ≤ ⌊log₂ n⌋ when D ≤ (⌊log₂ n⌋ + 1)^c (`StSixU`).
This file has definitions only. The statements `St…` are propositions. -/

@[expose] public section

namespace UniformInK

open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F PaddedDescent.F.Mark CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks

/-! ### Constants -/

/-- W = b²·D·Y for b = β + 3, D = 2^β and Y the number of binary digits of K. -/
def WofU (β K : ℕ) : ℕ := (β + 3) ^ 2 * 2 ^ β * K.size

/-- The constant in g·P ≤ G·W·n. -/
def GU (C₀ : ℕ) : ℕ := 2660 * (1 + 17 * C₀)

/-- The sum of the constants of the parts of lower order. -/
def ccU (k C₀ : ℕ) : ℕ := 3 + 3 * GU C₀ + (55 + 354 * k + GU C₀) + GU C₀ + 54 + 1 + C₀ * (85 * C₀ + 16) + 27 * (4 + 17 * C₀) + (17 + 51 * C₀)

/-- The parameter a of the plan: 2^(betaU k s) ≤ (⌊log₂ n⌋ + 1)^(a·k). -/
def aU (C C₀ : ℕ) : ℕ := 34 + 8 * C + 8 * C * C₀

/-- The constant of the inequality W ≤ A₁·K·e. -/
def A1U (C₀ : ℕ) : ℕ := 1 + (2 * C₀ + 2).factorial * 2 ^ (2 * C₀ + 2)

/-! ### The exponent -/

/-- The exponent `needU` is at most (354·k·35·k + cc·A₁ + 1)·n·e·(s+1), if W ≤ A₁·K·e. -/
def StNeedU : Prop := ∀ (Idx : Type) [Enc Idx] (S : Solver Idx) (i : Idx) (e : ℝ) (C₀ k n s A₁ : ℕ), 1 ≤ k → 2 ≤ S.K i → S.K i ^ 17 ≤ n → n < S.K i ^ (17 * C₀) →
  2 ^ betaU k s ≤ n + 1 → 0 < e → e ≤ 1 → 1 / (2 : ℝ) ^ s ≤ e → ((WofU (betaU k s) (S.K i) : ℕ) : ℝ) ≤ (A₁ : ℝ) * (S.K i) * e →
  (∀ lam B : ℕ, 1 ≤ lam → 1 ≤ B → (S.need (i, List.replicate lam (), List.replicate B ()) : ℝ) ≤
    e * (S.K i : ℝ) ^ 2 * lam + C₀ * (S.K i : ℝ) ^ 2 * Real.logb 2 (S.K i * (lam + B))) →
  (needU S k i n s : ℝ) ≤ ((354 * k * (35 * k) + ccU k C₀ * A₁ + 1 : ℕ) : ℝ) * n * e * ((s : ℝ) + 1)

/-! ### The inequality W ≤ A₁·K·e with a constant that does not depend on k, and bounds on 2^β -/

/-- W ≤ A₁·K·e if D⁶ ≤ K. -/
def StMasterU : Prop := ∀ (β K C₀ : ℕ) (e : ℝ), β + 3 ≤ 2 ^ β → 2 ≤ K → 1 / Real.logb 2 K ^ C₀ ≤ e → (2 ^ β) ^ 6 ≤ K →
  ((WofU β K : ℕ) : ℝ) ≤ (A1U C₀ : ℝ) * K * e

/-- 2^(betaU k s) ≤ (⌊log₂ n⌋ + 1)^(a·k) for a = `aU C C₀`, if 2 ≤ K ≤ n, 1/(log₂ K)^C₀ ≤ e and 2^s
≤ (2/e)^C. -/
def StDLogU : Prop := ∀ (K n s C C₀ k : ℕ) (e : ℝ), 2 ≤ K → K ≤ n → 1 / Real.logb 2 K ^ C₀ ≤ e → (2 : ℝ) ^ s ≤ (2 / e) ^ C →
  2 ^ betaU k s ≤ (Nat.log 2 n + 1) ^ (aU C C₀ * k)

/-- A number D ≤ (⌊log₂ n⌋ + 1)^c has D⁶ ≤ K, if 2·(102·C₀·c)² ≤ ⌊log₂ n⌋ and n < K^(17·C₀). -/
def StSixU : Prop := ∀ D c K n C₀ : ℕ, 1 ≤ c → 1 ≤ n → n < K ^ (17 * C₀) → D ≤ (Nat.log 2 n + 1) ^ c → 2 * (102 * C₀ * c) ^ 2 ≤ Nat.log 2 n → D ^ 6 ≤ K

/-- What is used of β = `betaU k s`. -/
def StBetaU : Prop := ∀ k s : ℕ, 1 ≤ k → k ≤ betaU k s ∧ betaU k s + 3 ≤ 2 ^ betaU k s ∧ betaU k s + 1 ≤ 35 * k * (s + 1)

end UniformInK
