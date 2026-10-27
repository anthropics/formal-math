/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import UniformInK.Top.ArithDefs
import ClauseBound.ParityChecks.ArithAux
import all ClauseBound.TopN.Arith
import all ClauseBound.TopN.ArithR
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # A bound on 2^(s0U k) in terms of k²

The lemma `two_pow_s0U_le`: for k ≥ 1, 2^(s0U k) ≤ 4k², so 2^s < 4k² for every s < s0U k. -/

namespace UniformInK.Arith

open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.ParityChecks

/-- 2^(s0U k) ≤ 4k². -/
theorem two_pow_s0U_le {k : ℕ} (hk : 1 ≤ k) : 2 ^ s0U k ≤ 4 * k ^ 2 := by
  have h1 : 2 ^ (k.size - 1) ≤ k := Nat.lt_size.1 (by have := Nat.size_pos.2 hk; omega)
  have h2 : k.size = (k.size - 1) + 1 := by have := Nat.size_pos.2 hk; omega
  have h3 : 2 ^ k.size ≤ 2 * k := by rw [h2, pow_succ]; omega
  calc 2 ^ s0U k = (2 ^ k.size) ^ 2 := by unfold s0U; rw [← pow_mul, Nat.mul_comm]
    _ ≤ (2 * k) ^ 2 := Nat.pow_le_pow_left h3 2
    _ = 4 * k ^ 2 := by ring

end UniformInK.Arith
