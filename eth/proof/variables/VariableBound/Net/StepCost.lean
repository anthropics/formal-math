/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Alg.TopNet
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Step 4 of Appendix D: the number of bits with which the clique solver is called

Step 4 of Appendix D: «Take a network on [g] with parameters P, B, τ and total U, and let L = ⌈(U +
gP/K)/K²⌉ and B′ = ⌈2gP/K⌉ + g²B.» The program calls the clique solver with the label length
`lamS K g U P` and the number of bits
`bitsS K g P B` of proof/rates/ClauseBound/Alg/TopNet.lean, which serve every network. This file
computes the second on g = 3K⁸ nodes: 2g/K = 6K⁷ (`two_g_div`), and so
bitsS = 6K⁷P + (6K⁸ + 36K¹⁵)B (`bitsS_eq`). -/

@[expose] public section

namespace VariableBound.Net.StepCost

open Groundwork ClauseBound.Alg

/-- 2g/K = 6K⁷ for g = 3K⁸ and K ≥ 1. -/
theorem two_g_div {K : ℕ} (hK : 1 ≤ K) : 2 * (3 * K ^ 8) / K = 6 * K ^ 7 :=
  Nat.div_eq_of_eq_mul_left hK (by ring)

/-- On g = 3K⁸ nodes, K ≥ 1, the number of bits of the program is 6K⁷P + (6K⁸ + 36K¹⁵)B. -/
theorem bitsS_eq {K : ℕ} (hK : 1 ≤ K) (P B : ℕ) : bitsS K (3 * K ^ 8) P B = 6 * K ^ 7 * P + (6 * K ^ 8 + 36 * K ^ 15) * B := by
  rw [bitsS, two_g_div hK]
  ring

end VariableBound.Net.StepCost
