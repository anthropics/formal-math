/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Printed.ThmVariablesADefs
import VariableBound.Printed.VariablesA.Level
import ClauseBound.TopN.End
import ClauseBound.Alg.End
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Two facts on logarithms for the bound of Theorem D (a)

`lg_div_facts`: 1 ≤ log(2/e) ≤ log(k/e) for k ≥ 3 and 0 < e ≤ 1. `lg_lt_log_succ`: log₂ n < ⌊log₂ n⌋ +
1 for n ≥ 1. -/

public section

namespace VariableBound.VariablesA

open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.End ClauseBound.TopN ClauseBound.TopN.End MainTheoremForms

variable {Idx : Type} [Enc Idx] {S : Solver Idx} {e : ℕ → ℝ} {C₀ : ℕ} (Q : S.Seq e C₀)

/-- 1 ≤ log(k/e) for k ≥ 3 and 0 < e ≤ 1; more precisely log(2/e) ≤ log(k/e) and 1 ≤ log(2/e). -/
theorem lg_div_facts {k : ℕ} {x : ℝ} (hk : 3 ≤ k) (h0 : 0 < x) (h1 : x ≤ 1) : 1 ≤ MainTheoremForms.lg (2 / x) ∧ MainTheoremForms.lg (2 / x) ≤ MainTheoremForms.lg (k / x) := by
  have hk' : (3 : ℝ) ≤ k := by exact_mod_cast hk
  constructor
  · rw [MainTheoremForms.lg, Real.le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_one, le_div_iff₀ h0]
    linarith
  · exact Real.logb_le_logb_of_le (by norm_num) (by positivity) (div_le_div_of_nonneg_right (by linarith) h0.le)

/-- log₂ n < ⌊log₂ n⌋ + 1, for n ≥ 1. -/
theorem lg_lt_log_succ {n : ℕ} (hn : 1 ≤ n) : MainTheoremForms.lg n < (Nat.log 2 n : ℝ) + 1 := by
  have h : (n : ℝ) < (2 : ℝ) ^ (Nat.log 2 n + 1) := by exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) n
  have h1 := Real.logb_lt_logb (b := 2) (by norm_num) (by exact_mod_cast hn) h
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h1
  simpa [MainTheoremForms.lg] using h1

end VariableBound.VariablesA
