/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.LevelNumbers
public import GeneralPieces.DefGenPieces.Conv
import Mathlib.Tactic

/-! # The bounds for λ and B, from one depth to the next

`lamAt` and `bitsAt` (`RecursionDefs.lean`) are the bounds Λ_j, 𝔅_j for λ and B at the depth j of
the recursion from an outermost instance (ℓ, λ, B). For j < ℓ, Λ_j is the floor of ((ρ +
3ζ_j)g_j⁴Λ_{j+1} + (c/4)g_j⁴log(2Λ_{j+1}) + K_j²)/K_j² and 𝔅_j is the B' of Lemma 8 for Λ_{j+1},
𝔅_{j+1} (`lamAt_of_lt`, `bitsAt_of_lt`).
From this `chainLabel`: 1 ≤ Λ_j ≤ g_j⁴Λ_{j+1} + 1, 1 ≤ 𝔅_j, and the outer inequality of «K²L ≤ U +
2ζN + K² ≤ (ρ + 3ζ)N + (c/4)g⁴log(2λ) + K²» for the bounds. -/

public section

namespace ExplicitCost

open Levels.Gen Printed

variable {ρ : ℝ} {c x₀ l lam B j : ℕ}

/-- At the depth ℓ the bound for λ is λ itself. -/
theorem lamAt_self (ρ : ℝ) (c x₀ l lam B : ℕ) : lamAt ρ c x₀ l lam B l = lam := by simp [lamAt, boundsDown]

/-- At the depth ℓ the bound for B is B itself. -/
theorem bitsAt_self (ρ : ℝ) (c x₀ l lam B : ℕ) : bitsAt ρ c x₀ l lam B l = B := by simp [bitsAt, boundsDown]

/-- Λ_j from Λ_{j+1}. -/
theorem lamAt_of_lt (ρ : ℝ) (c x₀ lam B : ℕ) (h : j < l) : lamAt ρ c x₀ l lam B j =
    ⌊((ρ + 3 * zeta j) * ((g x₀ j : ℝ) ^ 4 * lamAt ρ c x₀ l lam B (j + 1)) + (c : ℝ) / 4 * (g x₀ j : ℝ) ^ 4 * Real.logb 2 (2 * lamAt ρ c x₀ l lam B (j + 1)) + (K x₀ j : ℝ) ^ 2) / (K x₀ j : ℝ) ^ 2⌋₊ := by
  obtain ⟨k, hk⟩ : ∃ k, l - j = k + 1 := ⟨l - j - 1, by omega⟩
  have e1 : l - (j + 1) = k := by omega
  have e2 : l - (k + 1) = j := by omega
  unfold lamAt
  rw [hk, e1]
  simp only [boundsDown, e2]

/-- 𝔅_j from Λ_{j+1} and 𝔅_{j+1}. -/
theorem bitsAt_of_lt (ρ : ℝ) (c x₀ lam B : ℕ) (h : j < l) : bitsAt ρ c x₀ l lam B j =
    bitsOut (K x₀ j) (g x₀ j) (g x₀ j ^ 3 * lamAt ρ c x₀ l lam B (j + 1)) (bitsOne c (g x₀ j) (lamAt ρ c x₀ l lam B (j + 1)) (bitsAt ρ c x₀ l lam B (j + 1))) := by
  obtain ⟨k, hk⟩ : ∃ k, l - j = k + 1 := ⟨l - j - 1, by omega⟩
  have e1 : l - (j + 1) = k := by omega
  have e2 : l - (k + 1) = j := by omega
  unfold bitsAt lamAt
  rw [hk, e1]
  simp only [boundsDown, e2]

/-- 0 < ζ_j ≤ 1/32. -/
theorem zeta_bounds (j : ℕ) : 0 < zeta j ∧ zeta j ≤ 1 / 32 := by
  have h : (2 : ℝ) ^ 5 ≤ 2 ^ (j + 5) := pow_le_pow_right₀ (by norm_num) (by omega)
  unfold zeta
  refine ⟨by positivity, one_div_le_one_div_of_le (by norm_num) ?_⟩
  norm_num at h
  exact h

/-- The number whose floor is Λ_j lies between 1 and g⁴Λ + 1. -/
theorem quotient_bounds {r G4 Λ lg cc k2 : ℝ} (hr0 : 0 ≤ r) (hr2 : r ≤ 2) (hG : 0 ≤ G4) (hΛ : 0 ≤ Λ) (hlg0 : 0 ≤ lg) (hlg : lg ≤ Λ) (hc0 : 0 ≤ cc) (hk : 2 + cc / 4 ≤ k2) :
    1 ≤ (r * (G4 * Λ) + cc / 4 * G4 * lg + k2) / k2 ∧ (r * (G4 * Λ) + cc / 4 * G4 * lg + k2) / k2 ≤ G4 * Λ + 1 := by
  have hk0 : 0 < k2 := by linarith [div_nonneg hc0 (by norm_num : (0 : ℝ) ≤ 4)]
  have hc4 : 0 ≤ cc / 4 := div_nonneg hc0 (by norm_num)
  have hGΛ : 0 ≤ G4 * Λ := mul_nonneg hG hΛ
  have a1 : 0 ≤ r * (G4 * Λ) := mul_nonneg hr0 hGΛ
  have a2 : 0 ≤ cc / 4 * G4 * lg := mul_nonneg (mul_nonneg hc4 hG) hlg0
  have a3 : r * (G4 * Λ) ≤ 2 * (G4 * Λ) := mul_le_mul_of_nonneg_right hr2 hGΛ
  have a4 : cc / 4 * G4 * lg ≤ cc / 4 * G4 * Λ := mul_le_mul_of_nonneg_left hlg (mul_nonneg hc4 hG)
  have a5 : (2 + cc / 4) * (G4 * Λ) ≤ k2 * (G4 * Λ) := mul_le_mul_of_nonneg_right hk hGΛ
  constructor
  · rw [le_div_iff₀ hk0]
    linarith
  · rw [div_le_iff₀ hk0]
    nlinarith

/-- 2 + c/4 ≤ K_j². -/
theorem two_add_le_K_sq (hc : c + 5 ≤ 2 ^ x₀) (j : ℕ) : 2 + (c : ℝ) / 4 ≤ (K x₀ j : ℝ) ^ 2 := by
  have h1 : c + 5 ≤ K x₀ j := hc.trans (two_pow_le_K x₀ j)
  have h2 : ((c : ℝ) + 5) ≤ K x₀ j := by exact_mod_cast h1
  have h3 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  nlinarith

/-- The facts on the quotient, for the numbers of the depth j and any Λ ≥ 1 one level up. -/
theorem quotient_at (hN : Numbers ρ c x₀ lam B) (j : ℕ) {Λ : ℕ} (hΛ : 1 ≤ Λ) :
    1 ≤ ((ρ + 3 * zeta j) * ((g x₀ j : ℝ) ^ 4 * Λ) + (c : ℝ) / 4 * (g x₀ j : ℝ) ^ 4 * Real.logb 2 (2 * Λ) + (K x₀ j : ℝ) ^ 2) / (K x₀ j : ℝ) ^ 2 ∧
    ((ρ + 3 * zeta j) * ((g x₀ j : ℝ) ^ 4 * Λ) + (c : ℝ) / 4 * (g x₀ j : ℝ) ^ 4 * Real.logb 2 (2 * Λ) + (K x₀ j : ℝ) ^ 2) / (K x₀ j : ℝ) ^ 2 ≤ (g x₀ j : ℝ) ^ 4 * Λ + 1 :=
  quotient_bounds (by linarith [hN.rho_ge, (zeta_bounds j).1]) (by linarith [hN.rho_lt, (zeta_bounds j).2]) (by positivity) (Nat.cast_nonneg _) (GeneralPieces.DefGenPieces.logb_nonneg hΛ) (GeneralPieces.DefGenPieces.logb_le hΛ)
    (Nat.cast_nonneg _) (two_add_le_K_sq hN.x₀_c j)

/-- 1 ≤ Λ_j for every j ≤ ℓ. -/
theorem lamAt_pos (hN : Numbers ρ c x₀ lam B) (l : ℕ) : ∀ k j, j + k = l → 1 ≤ lamAt ρ c x₀ l lam B j := by
  intro k
  induction k with
  | zero =>
    intro j hj
    obtain rfl : j = l := by omega
    rw [lamAt_self]
    exact hN.lam_pos
  | succ k ih =>
    intro j hj
    rw [lamAt_of_lt ρ c x₀ lam B (by omega : j < l)]
    exact Nat.le_floor (by exact_mod_cast (quotient_at hN j (ih (j + 1) (by omega))).1)

/-- Λ_j ≥ 1. -/
theorem one_le_lamAt (hN : Numbers ρ c x₀ lam B) (hj : j ≤ l) : 1 ≤ lamAt ρ c x₀ l lam B j := lamAt_pos hN l (l - j) j (by omega)

/-- 1 ≤ 𝔅_j for every j ≤ ℓ. -/
theorem one_le_bitsAt (hN : Numbers ρ c x₀ lam B) (hj : j ≤ l) : 1 ≤ bitsAt ρ c x₀ l lam B j := by
  rcases Nat.lt_or_ge j l with h | h
  · rw [bitsAt_of_lt ρ c x₀ lam B h]
    have h1 := one_le_lamAt hN (by omega : j + 1 ≤ l)
    have h2 : 1 ≤ g x₀ j ^ 2 := Nat.pow_pos (g_pos x₀ j)
    have h3 : 1 ≤ (2 * lamAt ρ c x₀ l lam B (j + 1)) ^ c := Nat.pow_pos (by omega)
    have h4 : 1 ≤ g x₀ j ^ 2 * (2 * lamAt ρ c x₀ l lam B (j + 1)) ^ c := Nat.mul_pos h2 h3
    have h5 : 1 ≤ g x₀ j ^ 2 * bitsOne c (g x₀ j) (lamAt ρ c x₀ l lam B (j + 1)) (bitsAt ρ c x₀ l lam B (j + 1)) := Nat.mul_pos h2 (by unfold bitsOne; omega)
    exact h5.trans (Nat.le_add_left _ _)
  · obtain rfl : j = l := by omega
    rw [bitsAt_self]
    exact hN.B_pos

/-- `ChainLabel` holds: for j < ℓ, 1 ≤ Λ_j, 1 ≤ 𝔅_j, Λ_j ≤ g_j⁴Λ_{j+1} + 1, and K_j²Λ_j ≤ (ρ +
3ζ_j)g_j⁴Λ_{j+1} + (c/4)g_j⁴log(2Λ_{j+1}) + K_j². -/
theorem chainLabel : ChainLabel := by
  intro ρ c x₀ l lam B j hN hj
  have hΛ := one_le_lamAt hN (by omega : j + 1 ≤ l)
  obtain ⟨q1, q2⟩ := quotient_at hN j hΛ
  have hK : (0 : ℝ) < (K x₀ j : ℝ) ^ 2 := by
    have : (0 : ℝ) < K x₀ j := by exact_mod_cast K_pos x₀ j
    positivity
  refine ⟨one_le_lamAt hN hj.le, one_le_bitsAt hN hj.le, ?_, ?_⟩
  · rw [lamAt_of_lt ρ c x₀ lam B hj]
    exact Nat.floor_le_of_le (by push_cast; exact q2)
  · have h := Nat.floor_le (le_trans zero_le_one q1)
    rw [← lamAt_of_lt ρ c x₀ lam B hj] at h
    have h2 := mul_le_mul_of_nonneg_left h hK.le
    rwa [mul_div_cancel₀ _ hK.ne'] at h2

end ExplicitCost
