/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Paper.SecPseudocode_Algorithm
public import KSatStatement
import Mathlib.Tactic

/-! # Section 8 of the paper: two facts on the numbers K_ℓ of display (38)

This file proves two elementary facts on the numbers K_ℓ of display (38): K_ℓ > 0 (`levelK_pos`) and
K_{ℓ+1} ≥ 19·K_ℓ (`levelK_succ_ge`). -/

@[expose] public section

namespace SingleBitPieces

open Paper Groundwork

namespace SecPseudocode_Levels

/-- K_ℓ is positive. -/
theorem levelK_pos (ℓ : ℕ) : (0 : ℝ) < levelK ℓ := by
  exact_mod_cast lt_of_lt_of_le (by norm_num) (levelK_ge ℓ)

/-- K_{ℓ+1} ≥ 19·K_ℓ. -/
theorem levelK_succ_ge (ℓ : ℕ) : 19 * (levelK ℓ : ℝ) ≤ levelK (ℓ + 1) := by
  have h1 := levelK_ge ℓ
  have h2 : levelK ℓ * 64 ≤ levelK ℓ ^ 16 := by
    calc levelK ℓ * 64 ≤ levelK ℓ * levelK ℓ := Nat.mul_le_mul_left _ h1
      _ = levelK ℓ ^ 2 := (sq _).symm
      _ ≤ levelK ℓ ^ 16 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h3 : 19 * levelK ℓ ≤ levelK (ℓ + 1) := by
    simp only [levelK]
    omega
  exact_mod_cast h3

end SecPseudocode_Levels

open SecPseudocode_Levels

end SingleBitPieces
