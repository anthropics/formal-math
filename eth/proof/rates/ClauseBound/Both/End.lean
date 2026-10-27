/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Both.Defs
import ClauseBound.Alg.End

/-! # Monotonicity of the bound in m and of the number of steps of the padding machine

Two monotonicity facts: the bound in the number m of clauses grows with its constant (`bound_mono`),
and the number of steps q·(L + 2^E + 1)^q of the padding machine grows with the length L of the
input and with the exponent E (`steps_mono`). -/

public section

namespace ClauseBound.Both.End

open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks

/-- The bound in m grows with the constant. -/
theorem bound_mono {r : ℕ → ℝ} {D D' : ℕ} (h : D ≤ D') (k m : ℕ) (hr : 0 ≤ r m) : SatM.bound r D k m ≤ SatM.bound r D' k m := by
  unfold SatM.bound
  have hD : (D : ℝ) ≤ D' := by exact_mod_cast h
  refine Nat.floor_le_floor (mul_le_mul hD (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_) (by positivity) (by positivity))
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD (by positivity)) (by positivity)) hr

/-- The number of steps of the padding machine grows with the length of the input and with the
exponent. -/
theorem steps_mono (q : ℕ) {L L' E E' : ℕ} (hL : L ≤ L') (hE : E ≤ E') : q * (L + 2 ^ E + 1) ^ q ≤ q * (L' + 2 ^ E' + 1) ^ q :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.add_le_add hL (Nat.pow_le_pow_right (by norm_num) hE)) _) _)

end ClauseBound.Both.End
