/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Gen.Defs
public import ClauseBound.Gen.PartA

/-! # The general recursion: K_l nodes at the index of level l, and K_l ≥ 2

This file holds two facts on the levels of the general recursion of Theorem A of the paper, stated
with the definitions of
`proof/rates/ClauseBound/Gen/Defs.lean` and `proof/rates/ClauseBound/Alg/Interfaces.lean`: the index
of level l is the schedule of the steps from K_l nodes down to K₀ nodes, so the solver has K_l nodes
at that index; and K_l ≥ 2 for x₀ ≥ 18.
The facts on K_l of part (a) of Theorem A are in `proof/rates/ClauseBound/Gen/PartA.lean`. -/

public section

namespace ClauseBound.Gen

open Groundwork PaddedDescent.F ClauseBound.Alg Levels.Gen

namespace Seq

/-- The solver has K_l nodes at the index of level l. -/
theorem topK_idx (P : PiecesF) (x₀ l : ℕ) : topK (idx P x₀ l) = K x₀ l := by
  cases l with
  | zero => simp [topK, idx, sched, rep]
  | succ l => simp [topK, idx, sched, step, rep, Step.p, Step.d, K, g, sq]

/-- K_l ≥ 2. -/
theorem two_le_K (x₀ l : ℕ) (hx : 18 ≤ x₀) : 2 ≤ K x₀ l := by
  rw [K_eq]
  have := x_ge x₀ l hx
  calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ x x₀ l := Nat.pow_le_pow_right (by norm_num) (by omega)

end Seq

open ClauseBound.Gen.Seq

end ClauseBound.Gen
