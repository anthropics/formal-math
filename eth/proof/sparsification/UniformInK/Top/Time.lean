/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import UniformInK.Top.Defs
import ClauseBound.TopN.End
import ClauseBound.Alg.End
import WidthK.Decode

/-! # The length of the input code of a k-CNF, bounded by a power of n+2

For the code x = `SatM.enc k φ` of (k, φ), with φ a k-CNF on n variables and k ≥ 1, this file proves |x| +
1 ≤ (n+2)^(5k). -/

public section

namespace UniformInK

open Groundwork PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.Alg.End ClauseBound.TopN ClauseBound.TopN.End

namespace Time

/-- The length of the code of (k, φ), plus one, is at most (n+2)^(5k), for a k-CNF φ on n variables
and k ≥ 1. -/
theorem length_enc_succ_le {k n : ℕ} {φ : Sat3.CNF n} (hk : 1 ≤ k) (h : SatK.IsKCNF k φ) : (SatM.enc k φ).length + 1 ≤ (n + 2) ^ (5 * k) := by
  have h1 : (SatK.enc k φ).length + 1 ≤ (k * 2 ^ k + 1) * (n + 2) ^ (k + 1) := DecodeK.length_enc_succ_le (φ := φ) h
  have h2 : (SatM.enc k φ).length = k + 1 + (SatK.enc k φ).length := by
    unfold SatM.enc
    rw [List.length_append, List.length_cons, List.length_replicate]
    omega
  have hb : 2 ≤ n + 2 := by omega
  have hkk : k + 1 ≤ 2 ^ k := Nat.lt_two_pow_self
  have h3 : (2 : ℕ) ^ k ≤ (n + 2) ^ k := Nat.pow_le_pow_left hb k
  have h4 : k * 2 ^ k + 1 ≤ (n + 2) ^ (2 * k) := by
    calc k * 2 ^ k + 1 ≤ 2 ^ k * 2 ^ k := by nlinarith [Nat.one_le_two_pow (n := k)]
      _ ≤ (n + 2) ^ k * (n + 2) ^ k := Nat.mul_le_mul h3 h3
      _ = (n + 2) ^ (2 * k) := by rw [← pow_add]; congr 1; omega
  have h5 : (k * 2 ^ k + 1) * (n + 2) ^ (k + 1) ≤ (n + 2) ^ (3 * k + 1) := by
    calc (k * 2 ^ k + 1) * (n + 2) ^ (k + 1) ≤ (n + 2) ^ (2 * k) * (n + 2) ^ (k + 1) := Nat.mul_le_mul_right _ h4
      _ = (n + 2) ^ (3 * k + 1) := by rw [← pow_add]; congr 1; omega
  have h6 : k + 1 ≤ (n + 2) ^ (3 * k + 1) := (hkk.trans h3).trans (Nat.pow_le_pow_right (by omega) (by omega))
  calc (SatM.enc k φ).length + 1 ≤ 2 * (n + 2) ^ (3 * k + 1) := by omega
    _ ≤ (n + 2) * (n + 2) ^ (3 * k + 1) := Nat.mul_le_mul_right _ hb
    _ = (n + 2) ^ (3 * k + 2) := by rw [← pow_succ']
    _ ≤ (n + 2) ^ (5 * k) := Nat.pow_le_pow_right (by omega) (by omega)

end Time

end UniformInK
