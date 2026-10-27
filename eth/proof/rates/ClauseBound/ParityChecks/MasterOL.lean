/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.ParityChecks.TopDefs
public import ClauseBound.Gen.Defs
import ClauseBound.Gen.End
import all ClauseBound.TopN.Arith
import all ClauseBound.TopN.Gen

/-! # A lower bound on the rate function (for the bound in n of Theorem A (c), second statement)

The rate function `SatK.rN 1 α n`, that is log₂ log₂(n+4)/(log₂(n+4))^α, is at least
1/(c·(log₂(n+2))^c) for α ≤ 1 and c ≥ 2 (`le_rN`).
With α = log₂(1/ρ) it is the rate of the bound in n of Theorem A (c) for a fixed k. -/

@[expose] public section

namespace ClauseBound.ParityChecks

open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen Levels.Gen

end ClauseBound.ParityChecks

end

namespace ClauseBound.ParityChecks.MasterOL

open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.End Levels.Gen ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.TopN.GenN

/-- The function r is not too small: 1/(c·(log₂(n+2))^c) ≤ log₂ log₂(n+4)/(log₂(n+4))^α for α ≤ 1
and c ≥ 2. -/
theorem le_rN {α : ℝ} {c : ℕ} (ha1 : α ≤ 1) (hc : 2 ≤ c) (n : ℕ) : 1 / ((c : ℝ) * Real.logb 2 ((n : ℝ) + 2) ^ c) ≤ SatK.rN 1 α n := by
  have hy := two_le_log n
  have hz := one_le_loglog n
  have hL := ClauseBound.Gen.End.one_le_log n
  have h4 := log_four_le n
  unfold SatK.rN
  set y := Real.logb 2 ((n : ℝ) + 4)
  set z := Real.logb 2 y
  set L := Real.logb 2 ((n : ℝ) + 2)
  have hc' : (2 : ℝ) ≤ c := by exact_mod_cast hc
  have hyα : 0 < y ^ α := Real.rpow_pos_of_pos (by linarith) _
  have h1 : y ^ α ≤ (c : ℝ) * L ^ c := by
    calc y ^ α ≤ y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) ha1
      _ = y := Real.rpow_one y
      _ ≤ 2 * L := h4
      _ ≤ (c : ℝ) * L ^ c := by
          have : L ≤ L ^ c := le_self_pow₀ hL (by omega)
          nlinarith
  calc 1 / ((c : ℝ) * L ^ c) ≤ 1 / y ^ α := one_div_le_one_div_of_le hyα h1
    _ ≤ z ^ 1 / y ^ α := div_le_div_of_nonneg_right (by rw [pow_one]; exact hz) hyα.le

end ClauseBound.ParityChecks.MasterOL

namespace ClauseBound.ParityChecks

open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.End Levels.Gen ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.TopN.GenN

end ClauseBound.ParityChecks
