/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import UniformInK.Top.Defs
import UniformInK.Top.Leaves
import all ClauseBound.ParityChecks.BudgetOL
import PaddedDescent.Choice
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # The parameters of the top level fit, and a bound on the stack of the walk

`stParU : StParU`: for τ = 2^(4s+17) and β = `betaU k s`, leafCU τ k + 2 ≤ 2^β (a leaf has at most
leafCU τ k · n clauses), and τ is at least k² and 8k as soon as s ≥ `s0U k`.
`stack_le`: the stack of the walk through the counting tree has length at most 2^(betaU k s + 5k +
10 + (k+3)·size n) for τ = 2^(4s+17).
The counterpart of proof/rates/ClauseBound/ParityChecks/BudgetOL.lean, whose lemmas on powers of two
are used; here bsumU τ k = τ^(2k) is exactly 2^β
(`bsumU_tauOf`), and a path of the counting tree has at most bsumU τ k · n steps. -/

namespace UniformInK.Budget

open PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.TopN ClauseBound.ParityChecks ClauseBound.ParityChecks.BudgetOL UniformInK.Leaves

/-- 2·(θ 0 + … + θ (k-1)) + 2 ≤ τ^(2k) for k ≥ 1 and τ ≥ 8. -/
theorem leafCU_add_two_le {τ : ℕ} (hτ : 8 ≤ τ) {k : ℕ} (hk : 1 ≤ k) : leafCU τ k + 2 ≤ τ ^ (2 * k) := by
  unfold leafCU
  induction k, hk using Nat.le_induction with
  | base =>
    have h : 8 * 8 ≤ τ * τ := Nat.mul_le_mul hτ hτ
    rw [Finset.range_one, Finset.sum_singleton, Nat.mul_one, sq, show thetaU τ 0 = 1 from rfl]
    omega
  | succ k hk ih =>
    obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
    rw [Finset.sum_range_succ, show thetaU τ (i + 1) = 4 * τ ^ (2 * i + 1) from rfl]
    have e1 : τ ^ (2 * (i + 1)) = τ * τ ^ (2 * i + 1) := by rw [show 2 * (i + 1) = (2 * i + 1) + 1 by ring, pow_succ]; ring
    have e2 : τ ^ (2 * (i + 1 + 1)) = τ * τ * τ ^ (2 * (i + 1)) := by rw [show 2 * (i + 1 + 1) = 2 * (i + 1) + 2 by ring, pow_add]; ring
    have h1 : 8 * τ ^ (2 * i + 1) ≤ τ ^ (2 * (i + 1)) := by rw [e1]; exact Nat.mul_le_mul_right _ hτ
    have h2 : 2 * τ ^ (2 * (i + 1)) ≤ τ ^ (2 * (i + 1 + 1)) := by rw [e2]; exact Nat.mul_le_mul_right _ (by nlinarith)
    omega

/-- The stack of the walk: stackLenCU k τ n (inLen k n) ≤ 2^(betaU k s + 5k + 10 + (k+3)·size n) for
τ = 2^(4s+17). -/
theorem stack_le {k : ℕ} (hk : 1 ≤ k) (n s : ℕ) : stackLenCU k (tauOf s) n (inLen k n) ≤ 2 ^ (betaU k s + 5 * k + 10 + (k + 3) * Nat.size n) := by
  obtain ⟨β, hβ⟩ : ∃ β, β = betaU k s := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z, z = Nat.size n := ⟨_, rfl⟩
  obtain ⟨kz, hkz⟩ : ∃ kz, kz = k * z := ⟨_, rfl⟩
  have hn1 : n + 1 ≤ 2 ^ z := hz ▸ succ_le_size n
  have hcl : k * (3 * n + 5) + 10 ≤ 2 ^ (k + z + 4) := hz ▸ clause_le k n
  have hB1 : 1 ≤ 2 ^ β := Nat.one_le_two_pow
  have he : betaU k s + 5 * k + 10 + (k + 3) * Nat.size n = β + 5 * k + 10 + (kz + 3 * z) := by
    rw [← hβ, ← hz, hkz]
    ring
  rw [he]
  unfold stackLenCU
  rw [bsumU_tauOf, ← hβ]
  have b1 : 2 ^ β * n + 1 ≤ 2 ^ (β + z) := by
    calc 2 ^ β * n + 1 ≤ 2 ^ β * (n + 1) := by nlinarith
      _ ≤ 2 ^ β * 2 ^ z := Nat.mul_le_mul_left _ hn1
      _ = 2 ^ (β + z) := (pow_add _ _ _).symm
  have hin : inLen k n ≤ 2 ^ (3 * k + 1 + (kz + z)) := by
    have h := inLen_le k n
    rw [← hz, show (k + 1) * z = k * z + z by ring, ← hkz] at h
    exact h
  have b2 : 2 ^ k * inLen k n * (k * (3 * n + 5) + 10) ≤ 2 ^ (k + (3 * k + 1 + (kz + z)) + (k + z + 4)) :=
    mul_le_pow (mul_le_pow le_rfl hin) hcl
  have b3 : 2 * n * (2 * (3 * n + 5) + 10) + 8 ≤ 2 ^ (z + z + 6) := by
    have h1 : (n + 1) * (n + 1) ≤ 2 ^ z * 2 ^ z := Nat.mul_le_mul hn1 hn1
    have h2 : 2 * n * (2 * (3 * n + 5) + 10) + 8 ≤ 64 * ((n + 1) * (n + 1)) := by nlinarith
    calc 2 * n * (2 * (3 * n + 5) + 10) + 8 ≤ 64 * (2 ^ z * 2 ^ z) := h2.trans (Nat.mul_le_mul_left _ h1)
      _ = 2 ^ (z + z + 6) := by rw [pow_add, pow_add]; ring
  have b4 : 2 ^ k * inLen k n * (k * (3 * n + 5) + 10) + (2 * n * (2 * (3 * n + 5) + 10) + 8) ≤ 2 ^ (5 * k + 6 + kz + 2 * z) :=
    add_le_pow b2 b3 (by omega) (by omega)
  have b5 : (2 ^ β * n + 1) * (2 ^ k * inLen k n * (k * (3 * n + 5) + 10) + 2 * n * (2 * (3 * n + 5) + 10) + 8) ≤
      2 ^ (β + z + (5 * k + 6 + kz + 2 * z)) := by
    rw [Nat.add_assoc (2 ^ k * inLen k n * (k * (3 * n + 5) + 10))]
    exact mul_le_pow b1 b4
  have b6 : 3 * n + 16 ≤ 2 ^ (z + 4) := by rw [pow_add]; omega
  have b7 := add_le_pow (r := β + 5 * k + 10 + (kz + 3 * z)) b5 b6 (by omega) (by omega)
  rw [Nat.add_assoc]
  exact b7

end UniformInK.Budget

namespace UniformInK

open PaddedDescent ClauseBound.ParityChecks.BudgetOL UniformInK.Leaves UniformInK.Budget

/-- leafCU τ k + 2 ≤ 2^(betaU k s) for τ = 2^(4s+17) and k ≥ 1; and k² ≤ τ, 8k ≤ τ if s ≥ s0U k. -/
public theorem stParU : StParU := by
  intro k s hk
  have h17 := two_pow_le_tauOf s
  refine ⟨?_, fun hs => ?_⟩
  · rw [← bsumU_tauOf]
    exact leafCU_add_two_le (le_trans (by norm_num) h17) hk
  · have h1 : k ^ 2 ≤ 2 ^ s := sq_le_of_s0U_le hs
    have h2 : 8 * 2 ^ s ≤ tauOf s := by
      rw [tauOf, show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : k ≤ k ^ 2 := by nlinarith
    omega

end UniformInK
