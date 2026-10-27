/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.Chain
import Mathlib.Tactic

/-! # The bound of the theorem, from one depth to the next
Proof of Theorem A (b): 𝒯 = 2^{eK²L}(K(L + B'))^{C₀K²} ≤ 2^{e(ρ+3ζ)N}·Ξ^{cg⁴/4+K²+(c+5)C₀K²}; here
it is proved at the bounds Λ_j, 𝔅_j for λ and B (`level_le`, `boundBelowFrom`, `boundBelow`),
from the hypotheses `ChainLabel`, `ChainBase` and `ChainExponent`. The exponent of 2 is written
e_{j+1}N − 3N/K_j, which is e_j(ρ + 3ζ_j)N, with N = K_{j+1}²Λ_{j+1}.
From `BoundBelow` and the sentence on the exponent of Ξ (`ExponentFits`), both hypotheses here, it
follows that the bound of the depth j is at most that of the depth j + 1, for C₀ ≥ 2(c + 1)
(`levelBound_le_succ`, `levelBound_le_top`). -/

public section

namespace ExplicitCost

open Levels.Gen Printed

variable {ρ : ℝ} {c x₀ l lam B j : ℕ}

/-- 1 ≤ Λ_j, 𝔅_j for j ≤ ℓ, from `ChainLabel` (for j < ℓ) and the hypotheses on λ and B (for j = ℓ). -/
theorem pos_of_chainLabel (hL : ChainLabel) (hN : Numbers ρ c x₀ lam B) (hj : j ≤ l) : 1 ≤ lamAt ρ c x₀ l lam B j ∧ 1 ≤ bitsAt ρ c x₀ l lam B j := by
  rcases Nat.lt_or_ge j l with h | h
  · exact ⟨(hL ρ c x₀ l lam B j hN h).1, (hL ρ c x₀ l lam B j hN h).2.1⟩
  · obtain rfl : j = l := by omega
    rw [lamAt_self, bitsAt_self]
    exact ⟨hN.lam_pos, hN.B_pos⟩

/-- The base of the polynomial factor, as a real number. -/
theorem baseAt_cast (ρ : ℝ) (c x₀ l lam B j : ℕ) : (K x₀ j : ℝ) * ((lamAt ρ c x₀ l lam B j : ℝ) + bitsAt ρ c x₀ l lam B j) = (baseAt ρ c x₀ l lam B j : ℝ) := by
  unfold baseAt
  push_cast
  ring

/-- 4·Λ_{j+1} ≤ Ξ and 4 ≤ Ξ, for x₀ ≥ 1. -/
theorem four_mul_le_xiAt (hx : 1 ≤ x₀) (ρ : ℝ) (c l lam B j : ℕ) (hB : 1 ≤ bitsAt ρ c x₀ l lam B (j + 1)) : 4 * lamAt ρ c x₀ l lam B (j + 1) + 4 ≤ xiAt ρ c x₀ l lam B j := by
  have hp : 2 ^ 1 ≤ 2 ^ x₀ := Nat.pow_le_pow_right (by norm_num) hx
  have hg : 2 ≤ g x₀ j := le_trans hp (two_pow_le_g x₀ j)
  have h4 : 2 ^ 2 ≤ g x₀ j ^ 2 := Nat.pow_le_pow_left hg 2
  have := Nat.mul_le_mul h4 (le_refl (lamAt ρ c x₀ l lam B (j + 1) + bitsAt ρ c x₀ l lam B (j + 1)))
  unfold xiAt Xi
  omega

/-- 4 divides g⁴, for x₀ ≥ 1. -/
theorem four_mul_div_g (hx : 1 ≤ x₀) (j : ℕ) : 4 * (g x₀ j ^ 4 / 4) = g x₀ j ^ 4 := by
  have h1 : 2 ∣ g x₀ j := Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  have h2 : 2 ^ 4 ∣ g x₀ j ^ 4 := pow_dvd_pow_of_dvd h1 4
  exact Nat.mul_div_cancel' (Dvd.dvd.trans (by norm_num) h2)

/-- 𝒯 = 2^{eK²L}(K(L + B'))^{C₀K²} ≤ 2^{e(ρ+3ζ)N}·Ξ^{cg⁴/4+K²+(c+5)C₀K²}, at the bounds for λ and B. -/
theorem level_le (hL : ChainLabel) (hB : ChainBase) (hE : ChainExponent) (hN : Numbers ρ c x₀ lam B) (hj : j < l) (C₀ : ℕ) :
    levelBound ρ c x₀ C₀ l lam B j ≤
      (2 : ℝ) ^ (e ρ x₀ (j + 1) * (K x₀ (j + 1) : ℝ) ^ 2 * lamAt ρ c x₀ l lam B (j + 1) - 3 * ((K x₀ (j + 1) : ℝ) ^ 2 * lamAt ρ c x₀ l lam B (j + 1)) / K x₀ j) *
        (xiAt ρ c x₀ l lam B j : ℝ) ^ (c * (g x₀ j ^ 4 / 4) + K x₀ j ^ 2 + (c + 5) * C₀ * K x₀ j ^ 2) := by
  obtain ⟨hΛ, hBB⟩ := pos_of_chainLabel hL hN (by omega : j + 1 ≤ l)
  have hx1 : 1 ≤ x₀ := by have := hN.x₀_ge; omega
  have hXn := four_mul_le_xiAt hx1 ρ c l lam B j hBB
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = (xiAt ρ c x₀ l lam B j : ℝ) := ⟨_, rfl⟩
  rw [← hX]
  obtain ⟨Λ, hΛd⟩ : ∃ Λ : ℕ, Λ = lamAt ρ c x₀ l lam B (j + 1) := ⟨_, rfl⟩
  rw [← hΛd] at hΛ hXn
  have hX2 : 2 ≤ X := by rw [hX]; exact_mod_cast (by omega : 2 ≤ xiAt ρ c x₀ l lam B j)
  have hXΛ : 2 * (Λ : ℝ) ≤ X := by rw [hX]; exact_mod_cast (by omega : 2 * Λ ≤ xiAt ρ c x₀ l lam B j)
  have hΛ0 : (0 : ℝ) < 2 * (Λ : ℝ) := by have : (1 : ℝ) ≤ Λ := by exact_mod_cast hΛ
                                         linarith
  -- the polynomial factor
  have p1 : (baseAt ρ c x₀ l lam B j : ℝ) ≤ X ^ (c + 5) := by rw [hX]; exact_mod_cast hB ρ c x₀ l lam B j hN hj
  have p2 : (baseAt ρ c x₀ l lam B j : ℝ) ^ (C₀ * K x₀ j ^ 2) ≤ X ^ ((c + 5) * C₀ * K x₀ j ^ 2) := by
    calc (baseAt ρ c x₀ l lam B j : ℝ) ^ (C₀ * K x₀ j ^ 2) ≤ (X ^ (c + 5)) ^ (C₀ * K x₀ j ^ 2) := pow_le_pow_left₀ (Nat.cast_nonneg _) p1 _
      _ = X ^ ((c + 5) * C₀ * K x₀ j ^ 2) := by rw [← pow_mul, Nat.mul_assoc]
  -- the power of 2
  have q0 := hE ρ c x₀ l lam B j hN hj
  rw [← hΛd] at q0 ⊢
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = e ρ x₀ (j + 1) * (K x₀ (j + 1) : ℝ) ^ 2 * Λ - 3 * ((K x₀ (j + 1) : ℝ) ^ 2 * Λ) / K x₀ j := ⟨_, rfl⟩
  rw [← hx]
  have eA : (c : ℝ) / 4 * (K x₀ (j + 1) : ℝ) ^ 2 = ((c * (g x₀ j ^ 4 / 4) : ℕ) : ℝ) := by
    have h1 : ((4 * (g x₀ j ^ 4 / 4) : ℕ) : ℝ) = ((K x₀ (j + 1) ^ 2 : ℕ) : ℝ) := by rw [four_mul_div_g hx1, K_succ_sq]
    push_cast at h1 ⊢
    rw [← h1]
    ring
  have q1 : e ρ x₀ j * (K x₀ j : ℝ) ^ 2 * lamAt ρ c x₀ l lam B j ≤ x + ((c * (g x₀ j ^ 4 / 4) : ℕ) : ℝ) * Real.logb 2 (2 * Λ) + ((K x₀ j ^ 2 : ℕ) : ℝ) := by
    rw [← eA, hx]
    push_cast
    linarith
  have q2 : (2 : ℝ) ^ (((c * (g x₀ j ^ 4 / 4) : ℕ) : ℝ) * Real.logb 2 (2 * Λ)) = (2 * (Λ : ℝ)) ^ (c * (g x₀ j ^ 4 / 4)) := by
    rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hΛ0, Real.rpow_natCast]
  have q3 : (2 : ℝ) ^ (e ρ x₀ j * (K x₀ j : ℝ) ^ 2 * lamAt ρ c x₀ l lam B j) ≤ (2 : ℝ) ^ x * X ^ (c * (g x₀ j ^ 4 / 4)) * X ^ (K x₀ j ^ 2) := by
    calc (2 : ℝ) ^ (e ρ x₀ j * (K x₀ j : ℝ) ^ 2 * lamAt ρ c x₀ l lam B j) ≤ (2 : ℝ) ^ (x + ((c * (g x₀ j ^ 4 / 4) : ℕ) : ℝ) * Real.logb 2 (2 * Λ) + ((K x₀ j ^ 2 : ℕ) : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) q1
      _ = (2 : ℝ) ^ x * (2 * (Λ : ℝ)) ^ (c * (g x₀ j ^ 4 / 4)) * (2 : ℝ) ^ (K x₀ j ^ 2) := by
          rw [Real.rpow_add (by norm_num), Real.rpow_add (by norm_num), q2, Real.rpow_natCast]
      _ ≤ (2 : ℝ) ^ x * X ^ (c * (g x₀ j ^ 4 / 4)) * X ^ (K x₀ j ^ 2) := by
          have hp : (0 : ℝ) < (2 : ℝ) ^ x := Real.rpow_pos_of_pos (by norm_num) _
          exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hΛ0.le hXΛ _) hp.le) (pow_le_pow_left₀ (by norm_num) hX2 _) (by positivity) (by positivity)
  unfold levelBound timeBound
  rw [baseAt_cast]
  calc (2 : ℝ) ^ (e ρ x₀ j * (K x₀ j : ℝ) ^ 2 * lamAt ρ c x₀ l lam B j) * (baseAt ρ c x₀ l lam B j : ℝ) ^ (C₀ * K x₀ j ^ 2)
      ≤ ((2 : ℝ) ^ x * X ^ (c * (g x₀ j ^ 4 / 4)) * X ^ (K x₀ j ^ 2)) * X ^ ((c + 5) * C₀ * K x₀ j ^ 2) := mul_le_mul q3 p2 (by positivity) (by positivity)
    _ = (2 : ℝ) ^ x * X ^ (c * (g x₀ j ^ 4 / 4) + K x₀ j ^ 2 + (c + 5) * C₀ * K x₀ j ^ 2) := by rw [pow_add, pow_add]; ring

/-- `level_le` in the form of the statement `BoundBelowFrom`. -/
theorem boundBelowFrom : BoundBelowFrom := fun hL hB hE _ _ _ C₀ _ _ _ _ hN hj => level_le hL hB hE hN hj C₀

/-- **By the induction hypothesis and e ≤ 1, the 𝒯 of Lemma 8 may be taken as 𝒯 = 2^{eK²L}(K(L +
B'))^{C₀K²} ≤ 2^{e(ρ+3ζ)N}·Ξ^{cg⁴/4+K²+(c+5)C₀K²}.** -/
theorem boundBelow : BoundBelow := boundBelowFrom chainLabel chainBase chainExponent

/-- The bound of the depth j + 1, with Ξ for its base. -/
theorem levelBound_succ (ρ : ℝ) (c x₀ C₀ l lam B j : ℕ) : levelBound ρ c x₀ C₀ l lam B (j + 1) =
    (2 : ℝ) ^ (e ρ x₀ (j + 1) * (K x₀ (j + 1) : ℝ) ^ 2 * lamAt ρ c x₀ l lam B (j + 1)) * (xiAt ρ c x₀ l lam B j : ℝ) ^ (C₀ * K x₀ (j + 1) ^ 2) := by
  unfold levelBound timeBound
  rw [baseAt_cast, baseAt_succ]

/-- The bound of the depth j is at most that of the depth j + 1, for C₀ ≥ 2(c + 1). -/
theorem levelBound_le_succ (hL : ChainLabel) (hBl : BoundBelow) (hEF : ExponentFits) (hN : Numbers ρ c x₀ lam B) (hj : j < l) {C₀ : ℕ} (hC : 2 * (c + 1) ≤ C₀) :
    levelBound ρ c x₀ C₀ l lam B j ≤ levelBound ρ c x₀ C₀ l lam B (j + 1) := by
  refine (hBl ρ c x₀ C₀ l lam B j hN hj).trans ?_
  rw [levelBound_succ]
  obtain ⟨-, hBB⟩ := pos_of_chainLabel hL hN (by omega : j + 1 ≤ l)
  have hx1 : 1 ≤ x₀ := by have := hN.x₀_ge; omega
  have hXn := four_mul_le_xiAt hx1 ρ c l lam B j hBB
  have hX1 : (1 : ℝ) ≤ (xiAt ρ c x₀ l lam B j : ℝ) := by exact_mod_cast (by omega : 1 ≤ xiAt ρ c x₀ l lam B j)
  have hK : (0 : ℝ) < K x₀ j := by exact_mod_cast K_pos x₀ j
  have h1 := hEF c 0 C₀ x₀ j hN.x₀_ge hN.x₀_c (by omega)
  have h2 : c * (g x₀ j ^ 4 / 4) ≤ c * g x₀ j ^ 4 / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have := four_mul_div_g hx1 j
    calc c * (g x₀ j ^ 4 / 4) * 2 ≤ c * (4 * (g x₀ j ^ 4 / 4)) := by nlinarith [Nat.zero_le (c * (g x₀ j ^ 4 / 4))]
      _ = c * g x₀ j ^ 4 := by rw [this]
  refine mul_le_mul (Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_) (pow_le_pow_right₀ hX1 (by omega)) (by positivity) (by positivity)
  have : (0 : ℝ) ≤ 3 * ((K x₀ (j + 1) : ℝ) ^ 2 * lamAt ρ c x₀ l lam B (j + 1)) / K x₀ j := by positivity
  linarith

/-- So the bound of every depth j ≤ ℓ is at most the bound of the theorem for the outermost
instance. -/
theorem levelBound_le_top (hL : ChainLabel) (hBl : BoundBelow) (hEF : ExponentFits) (hN : Numbers ρ c x₀ lam B) {C₀ : ℕ} (hC : 2 * (c + 1) ≤ C₀) (l : ℕ) :
    ∀ k j, j + k = l → levelBound ρ c x₀ C₀ l lam B j ≤ timeBound ρ x₀ C₀ l lam B := by
  intro k
  induction k with
  | zero =>
    intro j hj
    obtain rfl : j = l := by omega
    unfold levelBound
    rw [lamAt_self, bitsAt_self]
  | succ k ih =>
    intro j hj
    exact (levelBound_le_succ hL hBl hEF hN (by omega) hC).trans (ih (j + 1) (by omega))

end ExplicitCost
