/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsificationLemma.Geo.Defs
import SparsificationLemma.Geo.Tau
import all UniformInK.Top.Leaves
import UniformInK.Top.Budget

/-! # The sparsification theorem for τ = 2^(4s+17), with 2^(−s) in the role of ε

`stThmS` is `stThmTau` at τ = `tauOf s` and ε = 1/2^s. That this τ is large enough for k and ε, if s
≥ `s0U k`, is `UniformInK.Leaves.tauOf_worksU` (proof/sparsification/UniformInK/Top/Leaves.lean). -/

public section

namespace SparsificationLemma.Geo

open Finset Groundwork Groundwork.Sparsify CountKSat UniformInK PaddedDescent

/-- The theorem for τ = 2^(4s+17) and s ≥ `s0U k`. -/
theorem stThmS : StThmS := by
  intro k n s φ hk hs hφ
  obtain ⟨t1, t2, t3, t4, t5⟩ := stThmTau k n (tauOf s) (1 / 2 ^ s) φ hk ((stParU k s hk).2 hs).2 (Leaves.tauOf_worksU hk hs) hφ
  have e : (1 : ℝ) / 2 ^ s * (n : ℝ) = (n : ℝ) / 2 ^ s := by ring
  rw [e] at t3
  refine ⟨t1, t2, t3, ?_, t4, fun Φ hΦ v => ?_⟩
  · have h2 : n < 2 ^ s * (n / 2 ^ s + 1) := Nat.lt_mul_div_succ n (by positivity)
    have h3 : (n : ℝ) ≤ (2 : ℝ) ^ s * ((n / 2 ^ s + 1 : ℕ) : ℝ) := by exact_mod_cast h2.le
    have h4 : (n : ℝ) / 2 ^ s ≤ ((n / 2 ^ s + 1 : ℕ) : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    have h5 : ((outTau k n (tauOf s) φ).length : ℝ) ≤ ((2 ^ (n / 2 ^ s + 1) : ℕ) : ℝ) := by
      calc ((outTau k n (tauOf s) φ).length : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 2 ^ s) := t3
        _ ≤ (2 : ℝ) ^ (((n / 2 ^ s + 1 : ℕ) : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h4
        _ = ((2 ^ (n / 2 ^ s + 1) : ℕ) : ℝ) := by rw [Real.rpow_natCast]; push_cast; ring
    exact_mod_cast h5
  · have := t5 Φ hΦ v
    rwa [← bsumU, Leaves.bsumU_tauOf] at this

end SparsificationLemma.Geo
