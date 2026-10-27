/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Gen.Defs

/-! # The parameter ρ = 1/√2 satisfies 1/2 ≤ ρ < 1

Theorem A of the paper turns pieces with parameters (ρ, c) (Definition 7, which asks for 1/2 ≤ ρ < 1)
into an algorithm for #k-SAT in time 2^{O(km/(log m)^α)} with α = log₂(1/ρ).
This file proves 1/2 ≤ 1/√2 and 1/√2 < 1, so that ρ = 1/√2, the ρ of Appendix B, meets this
condition. -/

public section

namespace ClauseBound.Inst.Half

/-- 1/2 ≤ 1/√2. -/
theorem half_le : (1 / 2 : ℝ) ≤ 1 / Real.sqrt 2 := by
  have h1 : Real.sqrt 2 ≤ 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
  exact one_div_le_one_div_of_le (Real.sqrt_pos.2 (by norm_num)) h1

/-- 1/√2 < 1. -/
theorem lt_one : 1 / Real.sqrt 2 < 1 := by
  have h1 : 1 < Real.sqrt 2 := Real.lt_sqrt (by norm_num) |>.2 (by norm_num)
  rw [div_lt_one (by linarith)]
  exact h1

end ClauseBound.Inst.Half
