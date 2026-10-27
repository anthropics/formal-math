/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import UniformInK.Top.Defs
import ClauseBound.TopN.Gen

/-! # Where k² exceeds a multiple of log n, k²·log₂ log₂(n+4)/(log₂(n+4))^α is bounded below, for α ≤ 1

`fallBack_rN_of`: `FallBack (SatK.rN 1 α)` for every α ≤ 1. Let ⌊log₂ n⌋ < B·k². Then L = log₂(n+4)
≤ ⌊log₂ n⌋ + 3 ≤ (B+4)·k². As log₂ L ≥ 1 and L^α ≤ L, the rate r(n) = log₂ L/L^α is at
least 1/L, so (B+4)·k²·r(n) ≥ 1. There the bound 2^{C·k²·n·r(n)} of the statement is at least 2ⁿ for
every C ≥ B + 4, and exhaustive counting is within it. -/

public section

namespace UniformInK.FallBack

open ClauseBound.TopN.GenN

/-- log₂(n+4) ≤ ⌊log₂ n⌋ + 3. -/
theorem logb_le (n : ℕ) : Real.logb 2 ((n : ℝ) + 4) ≤ (Nat.log 2 n : ℝ) + 3 := by
  have h1 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have h2 : 1 ≤ 2 ^ Nat.log 2 n := Nat.one_le_two_pow
  have h3 : n + 4 ≤ 2 ^ (Nat.log 2 n + 3) := by
    rw [pow_succ] at h1
    rw [pow_add]
    omega
  have h4 : (n : ℝ) + 4 ≤ (2 : ℝ) ^ (Nat.log 2 n + 3) := by exact_mod_cast h3
  rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity)]
  calc (n : ℝ) + 4 ≤ (2 : ℝ) ^ (Nat.log 2 n + 3) := h4
    _ = (2 : ℝ) ^ ((Nat.log 2 n : ℝ) + 3) := by
      rw [← Real.rpow_natCast]
      push_cast
      rfl

/-- The rate is at least 1/log₂(n+4). -/
theorem inv_le_rN {α : ℝ} (ha1 : α ≤ 1) (n : ℕ) : 1 / Real.logb 2 ((n : ℝ) + 4) ≤ SatK.rN 1 α n := by
  unfold SatK.rN
  have hL := two_le_log n
  have hLL := one_le_loglog n
  have hs : Real.logb 2 ((n : ℝ) + 4) ^ α ≤ Real.logb 2 ((n : ℝ) + 4) := by
    calc Real.logb 2 ((n : ℝ) + 4) ^ α ≤ Real.logb 2 ((n : ℝ) + 4) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) ha1
      _ = Real.logb 2 ((n : ℝ) + 4) := Real.rpow_one _
  have hp : 0 < Real.logb 2 ((n : ℝ) + 4) ^ α := Real.rpow_pos_of_pos (by linarith) _
  rw [pow_one]
  exact div_le_div₀ (by linarith) hLL hp hs

end UniformInK.FallBack

namespace UniformInK

open ClauseBound.TopN.GenN UniformInK.FallBack

/-- The rate log₂ log₂(n+4)/(log₂(n+4))^α, α ≤ 1, allows the fall-back to exhaustive counting. -/
theorem fallBack_rN_of {α : ℝ} (ha1 : α ≤ 1) : FallBack (SatK.rN 1 α) := by
  intro B
  refine ⟨B + 4, fun k n hk _ hlog => ?_⟩
  have hL := two_le_log n
  have hk1 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ (by exact_mod_cast hk)
  have hlog' : (Nat.log 2 n : ℝ) ≤ (B : ℝ) * (k : ℝ) ^ 2 := by exact_mod_cast hlog.le
  have hLk : Real.logb 2 ((n : ℝ) + 4) ≤ ((B + 4 : ℕ) : ℝ) * (k : ℝ) ^ 2 := by
    push_cast
    nlinarith [logb_le n]
  calc (1 : ℝ) = Real.logb 2 ((n : ℝ) + 4) * (1 / Real.logb 2 ((n : ℝ) + 4)) := by
        rw [mul_one_div, div_self (by linarith)]
    _ ≤ ((B + 4 : ℕ) : ℝ) * (k : ℝ) ^ 2 * SatK.rN 1 α n :=
        mul_le_mul hLk (inv_le_rN ha1 n) (by positivity) (by positivity)

end UniformInK
