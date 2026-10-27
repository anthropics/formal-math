/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Consequences.Defs
import SplitCount.Main
import SizeCircuit.Main
import Complement.Readers
import Eight.ViaGrouping.CorGraph
import GraphProblems.Read
import GraphProblems.Sets
import GraphProblems.Cert
import GraphProblems.SetTM
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-! # Two elementary bounds: c·(n + m + 2)^c and c·x

`size_square` bounds c·(n + m + 2)^c by 2c·(n + 2)^(2c) for m ≤ n², and `steps_double` bounds c·x by
2c·x for x ≥ 0, with c and 2c read as reals. -/

public section

namespace Consequences

open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight Eight.ViaGrouping SplitCount SizeCircuit Complement

/-- c·(n + m + 2)^c ≤ 2c·(n + 2)^(2c) for m ≤ n². -/
theorem size_square {c n m : ℕ} (hm : m ≤ n * n) : c * (n + m + 2) ^ c ≤ 2 * c * (n + 2) ^ (2 * c) := by
  have h1 : n + m + 2 ≤ (n + 2) ^ 2 := by nlinarith
  calc c * (n + m + 2) ^ c ≤ c * ((n + 2) ^ 2) ^ c := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 c)
    _ = c * (n + 2) ^ (2 * c) := by rw [← pow_mul]
    _ ≤ 2 * c * (n + 2) ^ (2 * c) := Nat.mul_le_mul_right _ (by omega)

/-- c·x ≤ 2c·x for x ≥ 0, with the numbers c and 2c read as reals. -/
theorem steps_double (c : ℕ) {x : ℝ} (hx : 0 ≤ x) : (c : ℝ) * x ≤ ((2 * c : ℕ) : ℝ) * x := by
  refine mul_le_mul_of_nonneg_right ?_ hx
  exact_mod_cast (by omega : c ≤ 2 * c)

end Consequences
