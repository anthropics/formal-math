/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.RecursionDefs
public import CountedRecursion.Numbers
import Mathlib.Tactic

/-! # The numbers K_ℓ and g_ℓ

Natural numbers only. Proof of Theorem A (b): (c + 5)K² ≤ 2^{x₀}K² ≤ g⁴/2, so the exponent of Ξ is
at most C₀K_{ℓ+1}² (`exponentFits`); and the first inequality k times (`chainLevels`). -/

public section

namespace ExplicitCost

open Levels.Gen

/-- K_{j+1} = g_j². -/
theorem K_succ_eq (x₀ j : ℕ) : K x₀ (j + 1) = g x₀ j ^ 2 := rfl

/-- K_{j+1}² = g_j⁴. -/
theorem K_succ_sq (x₀ j : ℕ) : K x₀ (j + 1) ^ 2 = g x₀ j ^ 4 := by rw [K_succ_eq, ← pow_mul]

/-- 2^{x₀} ≤ K_j. -/
theorem two_pow_le_K (x₀ j : ℕ) : 2 ^ x₀ ≤ K x₀ j := K_mono x₀ (Nat.zero_le j)

/-- 2^{x₀}K_j ≤ g_j. -/
theorem two_pow_mul_K_le_g (x₀ j : ℕ) : 2 ^ x₀ * K x₀ j ≤ g x₀ j :=
  Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- K_j ≤ g_j. -/
theorem K_le_g (x₀ j : ℕ) : K x₀ j ≤ g x₀ j := Nat.le_mul_of_pos_left _ (Nat.pow_pos (by norm_num))

/-- 2^{x₀} ≤ g_j. -/
theorem two_pow_le_g (x₀ j : ℕ) : 2 ^ x₀ ≤ g x₀ j := (two_pow_le_K x₀ j).trans (K_le_g x₀ j)

/-- g_j ≥ 1. -/
theorem g_pos (x₀ j : ℕ) : 1 ≤ g x₀ j := (K_pos x₀ j).trans (K_le_g x₀ j)

/-- 2^{x₀}K² ≤ g⁴/2, for x₀ ≥ 1. -/
theorem two_mul_pow_mul_K_sq_le {x₀ : ℕ} (hx : 1 ≤ x₀) (j : ℕ) : 2 * (2 ^ x₀ * K x₀ j ^ 2) ≤ g x₀ j ^ 4 := by
  have hp : 2 ≤ 2 ^ x₀ := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ x₀ := Nat.pow_le_pow_right (by norm_num) hx
  have h0 : 1 ≤ 2 ^ x₀ * K x₀ j := Nat.mul_pos (by omega) (K_pos x₀ j)
  have h1 : 2 * (2 ^ x₀ * K x₀ j ^ 2) ≤ (2 ^ x₀ * K x₀ j) ^ 2 := by
    have e : (2 ^ x₀ * K x₀ j) ^ 2 = 2 ^ x₀ * (2 ^ x₀ * K x₀ j ^ 2) := by ring
    rw [e]
    exact Nat.mul_le_mul_right _ hp
  have h2 : (2 ^ x₀ * K x₀ j) ^ 2 ≤ (2 ^ x₀ * K x₀ j) ^ 4 := Nat.pow_le_pow_right h0 (by norm_num)
  exact (h1.trans h2).trans (Nat.pow_le_pow_left (two_pow_mul_K_le_g x₀ j) 4)

/-- (c + 5)K² ≤ 2^{x₀}K² ≤ g⁴/2. -/
theorem two_mul_c_mul_K_sq_le {c x₀ : ℕ} (hx : 1 ≤ x₀) (hc : c + 5 ≤ 2 ^ x₀) (j : ℕ) : 2 * ((c + 5) * K x₀ j ^ 2) ≤ g x₀ j ^ 4 :=
  (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ hc)).trans (two_mul_pow_mul_K_sq_le hx j)

/-- g + K² ≤ g⁴, for x₀ ≥ 1. -/
theorem g_add_K_sq_le {x₀ : ℕ} (hx : 1 ≤ x₀) (j : ℕ) : g x₀ j + K x₀ j ^ 2 ≤ g x₀ j ^ 4 := by
  have hp : 2 ^ 1 ≤ 2 ^ x₀ := Nat.pow_le_pow_right (by norm_num) hx
  have hg : 2 ≤ g x₀ j := le_trans hp (two_pow_le_g x₀ j)
  have h1 : K x₀ j ^ 2 ≤ g x₀ j ^ 2 := Nat.pow_le_pow_left (K_le_g x₀ j) 2
  have h2 : g x₀ j ≤ g x₀ j ^ 2 := Nat.le_self_pow (by norm_num) _
  have h3 : 2 ^ 2 ≤ g x₀ j ^ 2 := Nat.pow_le_pow_left hg 2
  have h4 : g x₀ j ^ 4 = g x₀ j ^ 2 * g x₀ j ^ 2 := by ring
  have h5 := Nat.mul_le_mul_right (g x₀ j ^ 2) h3
  omega

/-- `ChainLevels`. -/
theorem chainLevels : ChainLevels := by
  intro c x₀ l k hx hc hk
  constructor
  · induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨j, hj⟩ : ∃ j, l - (k + 1) = j := ⟨_, rfl⟩
      have e : l - k = j + 1 := by omega
      have h1 := ih (by omega)
      rw [e, K_succ_sq] at h1
      rw [hj]
      have h2 := two_mul_c_mul_K_sq_le (by omega) hc j
      calc 2 ^ (k + 1) * (c + 5) ^ (k + 1) * K x₀ j ^ 2 = 2 ^ k * (c + 5) ^ k * (2 * ((c + 5) * K x₀ j ^ 2)) := by ring
        _ ≤ 2 ^ k * (c + 5) ^ k * g x₀ j ^ 4 := Nat.mul_le_mul_left _ h2
        _ ≤ K x₀ l ^ 2 := h1
  · clear hk
    induction l with
    | zero => simpa using K_pos x₀ 0
    | succ l ih =>
      have h0 : 1 ≤ 2 ^ x₀ * K x₀ l := Nat.mul_pos (Nat.pow_pos (by norm_num)) (K_pos x₀ l)
      calc (c + 5) ^ (l + 1) = (c + 5) * (c + 5) ^ l := by ring
        _ ≤ 2 ^ x₀ * K x₀ l := Nat.mul_le_mul hc ih
        _ ≤ (2 ^ x₀ * K x₀ l) ^ 2 := Nat.le_self_pow (by norm_num) _
        _ ≤ g x₀ l ^ 2 := Nat.pow_le_pow_left (two_pow_mul_K_le_g x₀ l) 2

/-- `ExponentFits`. -/
theorem exponentFits : ExponentFits := by
  intro c C₄ C₀ x₀ j hx hc hC
  rw [K_succ_sq]
  have hk := two_mul_c_mul_K_sq_le (by omega) hc j
  have hG := g_add_K_sq_le (x₀ := x₀) (by omega) j
  have hg : 1 ≤ g x₀ j ^ 4 := Nat.pow_pos (g_pos x₀ j)
  have h1 : c * g x₀ j ^ 4 / 2 ≤ c * g x₀ j ^ 4 := Nat.div_le_self _ _
  have h2 : C₄ ≤ C₄ * g x₀ j ^ 4 := Nat.le_mul_of_pos_right _ hg
  have h3 : 2 * (c * g x₀ j ^ 4 + C₄ * g x₀ j ^ 4 + g x₀ j ^ 4) ≤ C₀ * g x₀ j ^ 4 := by
    have := Nat.mul_le_mul_right (g x₀ j ^ 4) hC
    have e : 2 * (c + C₄ + 1) * g x₀ j ^ 4 = 2 * (c * g x₀ j ^ 4 + C₄ * g x₀ j ^ 4 + g x₀ j ^ 4) := by ring
    omega
  have h4 : 2 * ((c + 5) * C₀ * K x₀ j ^ 2) ≤ C₀ * g x₀ j ^ 4 := by
    have := Nat.mul_le_mul_left C₀ hk
    have e : C₀ * (2 * ((c + 5) * K x₀ j ^ 2)) = 2 * ((c + 5) * C₀ * K x₀ j ^ 2) := by ring
    omega
  omega

end ExplicitCost
