/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! A power is below an exponential: x^A ≤ C·2^(c·x) for every c > 0, with C depending on A and c
(`pow_le_two_rpow`). -/

namespace Groundwork.SatNet

/-- A power is below an exponential. -/
public theorem pow_le_two_rpow (A : ℕ) {c : ℝ} (hc : 0 < c) : ∃ C : ℕ, ∀ x : ℕ, (x : ℝ) ^ A ≤ C * (2 : ℝ) ^ (c * x) := by
  have hl : 0 < c * Real.log 2 := mul_pos hc (Real.log_pos one_lt_two)
  refine ⟨⌈(A.factorial : ℝ) / (c * Real.log 2) ^ A⌉₊, fun x => ?_⟩
  have h1 := Real.pow_div_factorial_le_exp (c * Real.log 2 * x) (by positivity) A
  have h2 : (2 : ℝ) ^ (c * x) = Real.exp (c * Real.log 2 * x) := by
    rw [Real.rpow_def_of_pos two_pos]; congr 1; ring
  have hf : (0 : ℝ) < A.factorial := by exact_mod_cast A.factorial_pos
  have h3 : (x : ℝ) ^ A = (A.factorial / (c * Real.log 2) ^ A) * ((c * Real.log 2 * x) ^ A / A.factorial) := by
    rw [mul_pow (c * Real.log 2)]; field_simp
  rw [h2, h3]
  exact mul_le_mul (Nat.le_ceil _) h1 (by positivity) (by positivity)

end Groundwork.SatNet
