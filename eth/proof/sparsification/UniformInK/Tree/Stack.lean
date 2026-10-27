/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import UniformInK.Tree.Defs
import all PaddedDescent.F.Top

/-! # The length of the word of a state of the counting walk

This file proves `StStateLenU` of proof/sparsification/UniformInK/Tree/Defs.lean:
`stackLenCU k τ n m` bounds the length of the word of a state of the counting walk at width k. It is
the counterpart at width k of
`CountKSatRate.stStateLen` (proof/consequences/CountKSatRate/Stack.lean). The bounds for the word of
a list and of a formula, `len_list_le` and `len_fml_le`, are those of
proof/rates/PaddedDescent/F/Top.lean. -/

public section

namespace UniformInK

open Groundwork CountKSat PaddedDescent PaddedDescent.F

/-- The word of a state of the counting walk has length at most `stackLenCU k τ n m`. -/
theorem stStateLenU : StStateLenU := by
  intro k τ n m c st h1 h2 hc
  have hnode : ∀ x ∈ st, len x ≤ 2 ^ k * m * (k * (3 * n + 5) + 10) + 2 * n * (2 * (3 * n + 5) + 10) + 6 := by
    intro x hx
    obtain ⟨a1, a2, a3, a4⟩ := h2 x hx
    have b1 := Top.len_fml_le (m := 2 ^ k * m) (x := x.1) (by rw [Nat.mul_comm]; exact a1) a3
    have b2 := Top.len_fml_le (m := 2 * n) (x := x.2) a2 a4
    obtain ⟨s, X⟩ := x
    rw [len_pair]
    simp only at b1 b2
    omega
  have hst := Top.len_list_le h1 hnode
  rw [Nat.add_assoc _ 6 2, show 6 + 2 = 8 from rfl] at hst
  have hsz : Nat.size c ≤ n + 1 := Nat.size_le.2 hc
  rw [len_pair, len_nat]
  unfold stackLenCU
  omega

end UniformInK
