/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.TopN.Defs
public import ClauseBound.Gen.Defs
import ClauseBound.Gen.End
import all ClauseBound.TopN.Arith

/-! # Three elementary bounds on the logarithms of n + 4 and n + 2, for a natural number n

For every natural number n: 2 ≤ log₂(n+4), 1 ≤ log₂ log₂(n+4) and log₂(n+4) ≤ 2·log₂(n+2). -/

@[expose] public section

namespace ClauseBound.TopN

open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen Levels.Gen

end ClauseBound.TopN

end

namespace ClauseBound.TopN.GenN

open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.End Levels.Gen ClauseBound.TopN.Arith

/-- 2 ≤ log₂(n+4). -/
public theorem two_le_log (n : ℕ) : (2 : ℝ) ≤ Real.logb 2 ((n : ℝ) + 4) := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
  norm_num

/-- 1 ≤ log₂ log₂(n+4). -/
public theorem one_le_loglog (n : ℕ) : (1 : ℝ) ≤ Real.logb 2 (Real.logb 2 ((n : ℝ) + 4)) := by
  have h := two_le_log n
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith), Real.rpow_one]
  exact h

/-- log₂(n+4) ≤ 2·log₂(n+2). -/
theorem log_four_le (n : ℕ) : Real.logb 2 ((n : ℝ) + 4) ≤ 2 * Real.logb 2 ((n : ℝ) + 2) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : (n : ℝ) + 4 ≤ ((n : ℝ) + 2) ^ 2 := by nlinarith
  calc Real.logb 2 ((n : ℝ) + 4) ≤ Real.logb 2 (((n : ℝ) + 2) ^ 2) := Real.logb_le_logb_of_le (by norm_num) (by positivity) h1
    _ = 2 * Real.logb 2 ((n : ℝ) + 2) := by rw [Real.logb_pow]; norm_num

end ClauseBound.TopN.GenN

namespace ClauseBound.TopN

open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.End Levels.Gen ClauseBound.TopN.Arith ClauseBound.TopN.GenN

end ClauseBound.TopN
