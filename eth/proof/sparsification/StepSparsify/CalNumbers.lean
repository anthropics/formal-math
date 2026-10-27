/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import StepSparsify.Defs
import SparsificationLemma.Cal.Alpha
import SparsificationLemma.Cal.Beta
import UniformInK.Top.Leaves
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-! # Calabro's numbers fit the bounds of the plan

This file proves `StAlphaS` and `StCalNumbers` of proof/sparsification/StepSparsify/Defs.lean.
Throughout K = max(k, 3), ε = 1/2^s, α = `alphaS k s` and τ = `tauOf s` = 2^(4s+17).
`stAlphaS`: with this ε the two numbers under a ceiling sign, x = 32(K−1)²·2^s and 2(K−1)²·2^s·⌈log₂
x⌉, are natural numbers, so the ceilings disappear.
`stCalNumbers`: K² ≤ α and 2 ≤ α are in `Cal.stAlpha`. By `Cal.stAlphaLe`, 32α ≤ (8K·2^s)³; as K ≤
3k and k ≤ k² ≤ 2^s, the base is at most 2^(2s+5), so 32α ≤ 2^(6s+15) ≤ τ² (`alpha_le`).
By fact (iv), β₁ + … + β_{k−1} ≤ 4·(32α)^(k−2) ≤ 4·τ^(2(k−2)) ≤ τ^(2k). By `Cal.stDegSum`, 2·(θ₀ + … +
θ_{k−1}) + 2 ≤ 18 + (32α)^(k−1) ≤ 18 + τ^(2(k−1)) ≤ τ^(2k) = 2^(2k(4s+17)).
For k = 1 the two sums are β₀ = 0 and θ₀ = 2. -/

public section

namespace StepSparsify

open Finset PaddedDescent UniformInK SparsificationLemma

/-- α without fractions: α = 2(K−1)²·2^s·⌈log₂(32(K−1)²·2^s)⌉ with K = max(k, 3). -/
theorem stAlphaS : StAlphaS := by
  intro k s
  obtain ⟨K, hK⟩ : ∃ K, max k 3 = K + 1 := ⟨max k 3 - 1, by omega⟩
  rw [alphaS, hK, Cal.alphaC, Cal.logC, Cal.xC, Nat.add_sub_cancel]
  have e1 : (32 : ℚ) * (((K + 1 : ℕ) : ℚ) - 1) ^ 2 / (1 / 2 ^ s) = ((32 * K ^ 2 * 2 ^ s : ℕ) : ℚ) := by
    push_cast
    field_simp
    ring
  rw [e1, Nat.ceil_natCast]
  have e2 : (2 : ℚ) * (((K + 1 : ℕ) : ℚ) - 1) ^ 2 / (1 / 2 ^ s) * ((Nat.clog 2 (32 * K ^ 2 * 2 ^ s) : ℕ) : ℚ)
      = ((2 * K ^ 2 * 2 ^ s * Nat.clog 2 (32 * K ^ 2 * 2 ^ s) : ℕ) : ℚ) := by
    push_cast
    field_simp
    ring
  rw [e2, Nat.ceil_natCast]

/-- ε = 1/2^s is positive. -/
theorem eps_pos (s : ℕ) : (0 : ℚ) < 1 / 2 ^ s := by positivity

/-- ε = 1/2^s is at most 1. -/
theorem eps_le_one (s : ℕ) : (1 : ℚ) / 2 ^ s ≤ 1 := by
  rw [div_le_one (by positivity)]
  exact one_le_pow₀ (by norm_num)

/-- 2 ≤ α and K² ≤ α, for all k and s. -/
theorem le_alphaS (k s : ℕ) : 2 ≤ alphaS k s ∧ max k 3 ^ 2 ≤ alphaS k s := by
  obtain ⟨-, a2, a3, -⟩ := Cal.stAlpha (max k 3) (1 / 2 ^ s) (le_max_right k 3) (eps_pos s) (eps_le_one s)
  exact ⟨a2, a3⟩

/-- 32α ≤ τ², for k ≥ 1 and k² ≤ 2^s. -/
theorem alpha_le {k s : ℕ} (hk : 1 ≤ k) (hs : k ^ 2 ≤ 2 ^ s) : 32 * alphaS k s ≤ tauOf s ^ 2 := by
  have h1 : 32 * (alphaS k s : ℝ) ≤ (8 * ((max k 3 : ℕ) : ℝ) / (((1 / 2 ^ s : ℚ)) : ℝ)) ^ 3 :=
    Cal.stAlphaLe (max k 3) (1 / 2 ^ s) (le_max_right k 3) (eps_pos s) (eps_le_one s)
  have e : (8 * ((max k 3 : ℕ) : ℝ) / (((1 / 2 ^ s : ℚ)) : ℝ)) ^ 3 = (((8 * max k 3 * 2 ^ s) ^ 3 : ℕ) : ℝ) := by
    push_cast
    field_simp
  rw [e] at h1
  have h2 : 32 * alphaS k s ≤ (8 * max k 3 * 2 ^ s) ^ 3 := by exact_mod_cast h1
  have h3 : max k 3 ≤ 3 * k := by omega
  have h4 : k ≤ 2 ^ s := le_trans (by nlinarith) hs
  have h5 : 8 * max k 3 * 2 ^ s ≤ 2 ^ (2 * s + 5) := by
    calc 8 * max k 3 * 2 ^ s ≤ 8 * (3 * 2 ^ s) * 2 ^ s :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (h3.trans (Nat.mul_le_mul_left _ h4)))
      _ ≤ 32 * (2 ^ s * 2 ^ s) := by nlinarith [Nat.zero_le (2 ^ s * 2 ^ s)]
      _ = 2 ^ (2 * s + 5) := by ring
  calc 32 * alphaS k s ≤ (8 * max k 3 * 2 ^ s) ^ 3 := h2
    _ ≤ (2 ^ (2 * s + 5)) ^ 3 := Nat.pow_le_pow_left h5 3
    _ = 2 ^ ((2 * s + 5) * 3) := by rw [← pow_mul]
    _ ≤ 2 ^ ((4 * s + 17) * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = tauOf s ^ 2 := by rw [tauOf, ← pow_mul]

/-- Calabro's numbers fit the bounds of the plan: 1 ≤ α, k² ≤ α, and the two sums are small enough. -/
theorem stCalNumbers : StCalNumbers := by
  intro k s hk hs
  obtain ⟨a2, a3⟩ := le_alphaS k s
  have hq := alpha_le hk (Leaves.sq_le_of_s0U_le hs)
  have hα : 1 ≤ alphaS k s := by omega
  have hT : 18 ≤ tauOf s ^ 2 := by
    calc 18 ≤ 2 ^ 5 := by norm_num
      _ ≤ 2 ^ ((4 * s + 17) * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = tauOf s ^ 2 := by rw [tauOf, ← pow_mul]
  have hb : bsumU (tauOf s) k = (tauOf s ^ 2) ^ k := by rw [bsumU, pow_mul]
  rw [← Leaves.bsumU_tauOf, hb]
  generalize tauOf s ^ 2 = T at hq hT
  refine ⟨hα, (Nat.pow_le_pow_left (le_max_left k 3) 2).trans a3, ?_, ?_⟩
  · obtain rfl | hk2 : k = 1 ∨ 2 ≤ k := by omega
    · simp [Cal.betaC_zero]
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      rw [Cal.sum_range_betaC _ hk]
      calc ∑ c ∈ Ico 1 (j + 2), Cal.betaC (alphaS (j + 2) s) c ≤ 4 * (32 * alphaS (j + 2) s) ^ j := Cal.factIV _ _ hα hk2
        _ ≤ 4 * T ^ j := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hq j)
        _ ≤ T ^ 2 * T ^ j := Nat.mul_le_mul_right _ (by nlinarith)
        _ = T ^ (j + 2) := by ring
  · obtain rfl | hk2 : k = 1 ∨ 2 ≤ k := by omega
    · simp only [lcCal, thCal, sum_range_one, Cal.thetaC, pow_one]
      omega
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      obtain ⟨-, d2, d3⟩ := Cal.stDegSum (alphaS (j + 2) s) (j + 2) hα hk2
      rw [Nat.add_sub_cancel] at d2 d3
      rw [show j + 2 - 1 = j + 1 by omega] at d3
      have h1 : (32 * alphaS (j + 2) s) ^ (j + 1) ≤ T ^ (j + 1) := Nat.pow_le_pow_left hq _
      have h2 : T ≤ T ^ (j + 1) := by
        calc T = T ^ 1 := (pow_one T).symm
          _ ≤ T ^ (j + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      have h3 : 2 * T ^ (j + 1) ≤ T ^ (j + 2) := by
        rw [pow_succ T (j + 1), Nat.mul_comm]
        exact Nat.mul_le_mul_left _ (by omega)
      rw [lcCal, thCal]
      omega

end StepSparsify
