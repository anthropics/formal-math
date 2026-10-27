/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import LevelsStatement

/-! # The exponents x_ℓ of the numbers K_ℓ of Theorem A (Appendix A)

The numbers K_ℓ of Theorem A are powers of two; their exponents x_ℓ satisfy x_{ℓ+1} = 2·x_ℓ + 6ℓ +
2·x₀. This file proves K_ℓ = 2^{x_ℓ}, log K_ℓ = x_ℓ,
x_ℓ ≥ x₀ + 2ℓ, ζ_ℓ > 0, and 2^10·(3x₀+6) ≤ 2^{x₀} for x₀ ≥ 18. -/

public section

namespace ClauseBound.Gen

open Levels.Gen

/-- x_ℓ, the exponent of K_ℓ. -/
@[expose] def x (x₀ : ℕ) : ℕ → ℕ
  | 0 => x₀
  | l + 1 => 2 * (3 * l + x₀ + x x₀ l)

/-- K_ℓ = 2^{x_ℓ}. -/
theorem K_eq (x₀ l : ℕ) : K x₀ l = 2 ^ x x₀ l := by
  induction l with
  | zero => rfl
  | succ l ih => rw [K, x, ih, ← pow_add, ← pow_mul, Nat.mul_comm]

/-- x_ℓ ≥ x₀ + 2ℓ. -/
theorem x_ge (x₀ l : ℕ) (hx : 18 ≤ x₀) : x₀ + 2 * l ≤ x x₀ l := by
  induction l with
  | zero => simp [x]
  | succ l ih => rw [x]; omega

/-- The real number K_ℓ is 2^{x_ℓ}. -/
theorem K_cast (x₀ l : ℕ) : (K x₀ l : ℝ) = 2 ^ x x₀ l := by
  rw [K_eq]; push_cast; rfl

/-- log K_ℓ = x_ℓ. -/
theorem logb_K (x₀ l : ℕ) : Real.logb 2 (K x₀ l) = x x₀ l := by
  rw [K_cast, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]

/-- ζ_ℓ > 0. -/
theorem zeta_pos (l : ℕ) : 0 < zeta l := by unfold zeta; positivity

/-- 2^10·(3x₀+6) ≤ 2^{x₀} for x₀ ≥ 18. -/
theorem pow_x₀ (x₀ : ℕ) (hx : 18 ≤ x₀) : 2 ^ 10 * (3 * x₀ + 6) ≤ 2 ^ x₀ := by
  induction x₀, hx using Nat.le_induction with
  | base => norm_num
  | succ n hn ih => rw [pow_succ]; omega

end ClauseBound.Gen
