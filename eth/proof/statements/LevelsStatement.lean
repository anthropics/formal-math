/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # The schedule of levels of Theorem A and part (a) of Theorem A (pure mathematics; definitions and statements only; imports Mathlib only) -/

@[expose] public section

namespace Levels

/-! ## The general recursion: K₀ = 2^{x₀}, e₀ = 1/2, ζ_ℓ = 2^{−ℓ−5}, g_ℓ = 2^{3ℓ+x₀}·K_ℓ, K_{ℓ+1} = g_ℓ², e_{ℓ+1} = (ρ + 3ζ_ℓ)·e_ℓ + 3/K_ℓ -/

namespace Gen

/-- K_ℓ. -/
def K (x₀ : ℕ) : ℕ → ℕ
  | 0 => 2 ^ x₀
  | l + 1 => (2 ^ (3 * l + x₀) * K x₀ l) ^ 2

/-- g_ℓ. -/
def g (x₀ l : ℕ) : ℕ := 2 ^ (3 * l + x₀) * K x₀ l

/-- ζ_ℓ. -/
noncomputable def zeta (l : ℕ) : ℝ := 1 / 2 ^ (l + 5)

/-- e_ℓ. -/
noncomputable def e (ρ : ℝ) (x₀ : ℕ) : ℕ → ℝ
  | 0 => 1 / 2
  | l + 1 => (ρ + 3 * zeta l) * e ρ x₀ l + 3 / K x₀ l

/-- Part (a) of Theorem A, on the general recursion. -/
structure PartA : Prop where
  logK : ∀ x₀ l : ℕ, Real.logb 2 (K x₀ l) = (3 * x₀ + 6) * 2 ^ l - 6 * l - 2 * x₀ - 6
  K_lt : ∀ x₀ l : ℕ, 18 ≤ x₀ → K x₀ l < K x₀ (l + 1)
  K_le : ∀ x₀ l : ℕ, 18 ≤ x₀ → K x₀ (l + 1) ≤ K x₀ l ^ 10
  e_ge : ∀ (ρ : ℝ) (x₀ l : ℕ), 1 / 2 ≤ ρ → ρ < 1 → 18 ≤ x₀ → ρ ^ l / 2 ≤ e ρ x₀ l
  e_le : ∀ (ρ : ℝ) (x₀ l : ℕ), 1 / 2 ≤ ρ → ρ < 1 → 18 ≤ x₀ → e ρ x₀ l ≤ 0.85 * ρ ^ l
  rho_pow : ∀ (ρ : ℝ) (x₀ l : ℕ), 1 / 2 ≤ ρ → ρ < 1 → 18 ≤ x₀ →
    ρ ^ l ≤ ((3 * x₀ + 6) / Real.logb 2 (K x₀ l)) ^ Real.logb 2 (1 / ρ)
  /-- the condition of case (ii) of Lemma 8 at every level -/
  case_ii : ∀ x₀ l : ℕ, 18 ≤ x₀ → (K x₀ l : ℝ) * Real.log (2 * g x₀ l * K x₀ l) ≤ 2 * zeta l ^ 2 * g x₀ l

end Gen


namespace Thin

end Thin

end Levels
