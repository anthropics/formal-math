/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Top.Defs
import all UniformInK.Top.Budget
import all ClauseBound.ParityChecks.BudgetOL

/-! # What a pad of length 2^(restD …) suffices for

`stBudgetD : UniformInK.StLeavesU → StBudgetD`: the list of profiles, the list of checks, the rounds
of the walk through the counting tree and its stack. Each of the four summands of `restD` pays for
one of the four budgets.
The first two budgets are proper to this file: a profile has two kinds of marks in place of three
layers, and the second summand of `restD` is the bit length of the
second budget itself. The last two budgets are those of
proof/sparsification/UniformInK/Top/Budget.lean, and its lemmas are used. -/

namespace VariableBound.Budget

open PaddedDescent.F ClauseBound.ParityChecks.BudgetOL

/-- The list of profiles: (M + 1)^(g·g·2) ≤ 2^(g·g·2·size M). -/
theorem nProf_le (g M : ℕ) : Mark.nProf g M 2 ≤ 2 ^ (g * g * 2 * Nat.size M) := by
  unfold Mark.nProf
  calc (M + 1) ^ (g * g * 2) ≤ (2 ^ Nat.size M) ^ (g * g * 2) := Nat.pow_le_pow_left (succ_le_size M) _
    _ = 2 ^ (g * g * 2 * Nat.size M) := by rw [← pow_mul, Nat.mul_comm (Nat.size M)]

end VariableBound.Budget

namespace VariableBound

open PaddedDescent ClauseBound.ParityChecks.BudgetOL UniformInK VariableBound.Net

/-- For k ≥ 1 and s ≥ s0U k, a number F ≥ 2^(restD k K n s) is at least the first, second and fourth
budgets, and F + 1 is at least the third, given the bound for the number of leaves
(`UniformInK.StLeavesU`). -/
public theorem stBudgetD (hL : StLeavesU) : StBudgetD := by
  intro k K n s F hk hs hF
  have up : ∀ {x t : ℕ}, x ≤ 2 ^ t → t ≤ restD k K n s → x ≤ F := fun h1 h2 => h1.trans ((Nat.pow_le_pow_right (by norm_num) h2).trans hF)
  refine ⟨up (Budget.nProf_le _ _) (le_four _ _ _ _).1, up (Nat.lt_size_self _).le (le_four _ _ _ _).2.1, ?_, up (UniformInK.Budget.stack_le hk n s) (le_four _ _ _ _).2.2.2⟩
  have h1 := hL k n s hk hs
  have h2 : 2 ^ (n / 2 ^ s + 1 + 1) ≤ F := up le_rfl (le_four _ _ _ _).2.2.1
  rw [pow_succ] at h2
  omega

end VariableBound
