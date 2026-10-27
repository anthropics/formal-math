/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.LevelBound
public import GeneralPieces.Rec.Rate
import Mathlib.Tactic

/-! # The count at the depth 0

In the proof of Theorem A (b), for ℓ = 0 brute force sums 2^{λK₀(K₀−1)/2} ≤ 2^{e₀K₀²λ} terms, each
at a cost of at most (K₀(λ+B))^{C₅}. The cost of the solver at the depth 0 is written out in
`solverCost`: 2^{λK₀(K₀−1)/2}·(K₀ + 1 + K₀t) if a query to the tables costs t.
For t ≥ 1 this is at most t times the bound of the theorem, for every C₀ ≥ 1: K₀ + 1 + K₀t ≤ 3K₀t ≤
t·(2K₀)² ≤ t·(K₀(λ+B))^{C₀K₀²}; the inequality of the exponents of 2 is
`GeneralPieces.Rate.brute_le`. -/

public section

namespace ExplicitCost

open Levels.Gen Printed

/-- The arithmetic on natural numbers: A(k + 1) + Akt ≤ t·(A·X^n) for 1 ≤ k, 2k ≤ X, n ≥ 2, t ≥ 1. -/
theorem base_count {A k X n t : ℕ} (hk : 1 ≤ k) (hX : 2 * k ≤ X) (hn : 2 ≤ n) (ht : 1 ≤ t) : A * (k + 1) + 0 * 0 + A * k * t ≤ t * (A * X ^ n) := by
  have h1 : (2 * k) ^ 2 ≤ X ^ n := (Nat.pow_le_pow_left hX 2).trans (Nat.pow_le_pow_right (by omega) hn)
  have h2 : 3 * k ≤ (2 * k) ^ 2 := by
    have a := Nat.le_mul_self k
    have e : (2 * k) ^ 2 = 4 * (k * k) := by ring
    omega
  have h3 : k + 1 + k * t ≤ t * (3 * k) := by
    have a : k ≤ k * t := Nat.le_mul_of_pos_right _ ht
    have e : t * (3 * k) = 3 * (k * t) := by ring
    omega
  calc A * (k + 1) + 0 * 0 + A * k * t = A * (k + 1 + k * t) := by ring
    _ ≤ A * (t * X ^ n) := Nat.mul_le_mul_left _ (h3.trans (Nat.mul_le_mul_left _ (h2.trans h1)))
    _ = t * (A * X ^ n) := by ring

/-- `CountBaseFrom`. -/
theorem countBaseFrom : CountBaseFrom := by
  intro hL C ρ c x₀ C₀ l lam B t hN hC ht
  obtain ⟨hΛ, hBB⟩ := pos_of_chainLabel hL hN (Nat.zero_le l)
  have hk : 2 ^ 1 ≤ 2 ^ x₀ := Nat.pow_le_pow_right (by norm_num) (by have := hN.x₀_ge; omega)
  have hX : 2 * 2 ^ x₀ ≤ baseAt ρ c x₀ l lam B 0 := by
    have : 2 ^ x₀ * 2 ≤ 2 ^ x₀ * (lamAt ρ c x₀ l lam B 0 + bitsAt ρ c x₀ l lam B 0) := Nat.mul_le_mul_left _ (by omega)
    change 2 * 2 ^ x₀ ≤ 2 ^ x₀ * (lamAt ρ c x₀ l lam B 0 + bitsAt ρ c x₀ l lam B 0)
    omega
  have hn : 2 ≤ C₀ * K x₀ 0 ^ 2 := by
    have h1 : 2 ^ 2 ≤ (2 ^ x₀) ^ 2 := Nat.pow_le_pow_left hk 2
    have h2 : 1 * (2 ^ x₀) ^ 2 ≤ C₀ * (2 ^ x₀) ^ 2 := Nat.mul_le_mul_right _ hC
    change 2 ≤ C₀ * (2 ^ x₀) ^ 2
    omega
  have h := base_count (A := 2 ^ (2 ^ x₀ * (2 ^ x₀ - 1) / 2 * lamAt ρ c x₀ l lam B 0)) (by omega : 1 ≤ 2 ^ x₀) hX hn ht
  have h' : solverCost C ρ c x₀ l lam B 0 0 t ≤ t * (2 ^ (2 ^ x₀ * (2 ^ x₀ - 1) / 2 * lamAt ρ c x₀ l lam B 0) * baseAt ρ c x₀ l lam B 0 ^ (C₀ * K x₀ 0 ^ 2)) := h
  have hr : (solverCost C ρ c x₀ l lam B 0 0 t : ℝ) ≤ t * ((2 : ℝ) ^ (2 ^ x₀ * (2 ^ x₀ - 1) / 2 * lamAt ρ c x₀ l lam B 0) * (baseAt ρ c x₀ l lam B 0 : ℝ) ^ (C₀ * K x₀ 0 ^ 2)) := by exact_mod_cast h'
  refine hr.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
  unfold levelBound timeBound
  rw [baseAt_cast]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [← Real.rpow_natCast (2 : ℝ) (2 ^ x₀ * (2 ^ x₀ - 1) / 2 * lamAt ρ c x₀ l lam B 0)]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (GeneralPieces.Rate.brute_le ρ x₀ (lamAt ρ c x₀ l lam B 0))

/-- `CountBase`. -/
theorem countBase : CountBase := countBaseFrom chainLabel

end ExplicitCost
