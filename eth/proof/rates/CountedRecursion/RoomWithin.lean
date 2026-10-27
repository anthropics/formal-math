/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.LevelBound
import Mathlib.Tactic

/-! # The room of the algorithm of the pieces

The paper bounds no memory. The largest label length of the recursion is Λ_j for some depth j ≤ ℓ;
with X_j = K_j(Λ_j + 𝔅_j), `room c Λ_j` = (2^{cΛ_j} + (2Λ_j)^c + 8)((2Λ_j)^c + 8) ≤
2^{cΛ_j}·X_j^{2c+3} (`room_le_aux`),
and c ≤ e_jK_j² (`c_le_e_mul`: e_j ≥ 2^{−j−1}, 2^j(c + 5)^jK_0² ≤ K_j²). So the room at Λ_j is at
most the bound of the theorem for depth j, with C₀ = 2c + 3, hence at most that of the outermost
instance (`levelBound_le_top`). -/

public section

namespace ExplicitCost

open Levels.Gen Printed Finset

/-- (u + P + 8)(P + 8) ≤ u·X^{2c+3}, for P ≤ X^c, 8 ≤ X, c ≥ 1, u ≥ 1. -/
theorem room_le_aux {u P X c : ℕ} (hP : P ≤ X ^ c) (hX : 8 ≤ X) (hc : 1 ≤ c) (hu : 1 ≤ u) : (u + P + 8) * (P + 8) ≤ u * X ^ (2 * c + 3) := by
  have h1 : X ≤ X ^ c := Nat.le_self_pow (by omega) _
  have h2 : P + 8 ≤ X ^ (c + 1) := by
    have : 2 * X ^ c ≤ X * X ^ c := Nat.mul_le_mul_right _ (by omega)
    have e : X ^ (c + 1) = X * X ^ c := by ring
    omega
  have h3 : 1 ≤ X ^ (c + 1) := Nat.pow_pos (by omega)
  have h4 : u + P + 8 ≤ u * X ^ (c + 2) := by
    have a1 : u ≤ u * X ^ (c + 1) := Nat.le_mul_of_pos_right _ h3
    have a2 : X ^ (c + 1) ≤ u * X ^ (c + 1) := Nat.le_mul_of_pos_left _ hu
    have a3 : 2 * (u * X ^ (c + 1)) ≤ X * (u * X ^ (c + 1)) := Nat.mul_le_mul_right _ (by omega)
    have e : u * X ^ (c + 2) = X * (u * X ^ (c + 1)) := by ring
    omega
  calc (u + P + 8) * (P + 8) ≤ (u * X ^ (c + 2)) * X ^ (c + 1) := Nat.mul_le_mul h4 h2
    _ = u * X ^ (2 * c + 3) := by ring

/-- c ≤ e_jK_j². -/
theorem c_le_e_mul (hLv : ChainLevels) (hA : Levels.Gen.PartA) {ρ : ℝ} {c x₀ lam B : ℕ} (hN : Numbers ρ c x₀ lam B) (j : ℕ) : (c : ℝ) ≤ e ρ x₀ j * (K x₀ j : ℝ) ^ 2 := by
  have h1 := (hLv c x₀ j j hN.x₀_ge hN.x₀_c le_rfl).1
  rw [Nat.sub_self] at h1
  have h2 : ((2 : ℝ) ^ j * ((c : ℝ) + 5) ^ j * ((2 : ℝ) ^ x₀) ^ 2) ≤ (K x₀ j : ℝ) ^ 2 := by exact_mod_cast h1
  have h3 := hA.e_ge ρ x₀ j hN.rho_ge hN.rho_lt hN.x₀_ge
  have h4 : (1 / 2 : ℝ) ^ j ≤ ρ ^ j := pow_le_pow_left₀ (by norm_num) hN.rho_ge j
  have h5 : (1 : ℝ) ≤ ((c : ℝ) + 5) ^ j := one_le_pow₀ (by have : (0 : ℝ) ≤ c := Nat.cast_nonneg _
                                                           linarith)
  have h6 : ((c : ℝ) + 5) ≤ (2 : ℝ) ^ x₀ := by exact_mod_cast hN.x₀_c
  have h7 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  have h8 : 2 * (c : ℝ) ≤ ((2 : ℝ) ^ x₀) ^ 2 := by nlinarith
  have h9 : (1 / 2 : ℝ) ^ j * (2 : ℝ) ^ j = 1 := by rw [← mul_pow]; norm_num
  have hp : (0 : ℝ) < (1 / 2 : ℝ) ^ j := by positivity
  have hq : (0 : ℝ) ≤ ((2 : ℝ) ^ x₀) ^ 2 := by positivity
  calc (c : ℝ) ≤ ((2 : ℝ) ^ x₀) ^ 2 / 2 := by linarith
    _ ≤ (((c : ℝ) + 5) ^ j * ((2 : ℝ) ^ x₀) ^ 2) / 2 := by
        have := mul_le_mul_of_nonneg_right h5 hq
        linarith
    _ = (1 / 2 : ℝ) ^ j / 2 * ((2 : ℝ) ^ j * ((c : ℝ) + 5) ^ j * ((2 : ℝ) ^ x₀) ^ 2) := by
        have : (1 / 2 : ℝ) ^ j / 2 * ((2 : ℝ) ^ j * ((c : ℝ) + 5) ^ j * ((2 : ℝ) ^ x₀) ^ 2) = ((1 / 2 : ℝ) ^ j * (2 : ℝ) ^ j) * ((((c : ℝ) + 5) ^ j * ((2 : ℝ) ^ x₀) ^ 2) / 2) := by ring
        rw [this, h9, one_mul]
    _ ≤ e ρ x₀ j * (K x₀ j : ℝ) ^ 2 := mul_le_mul (by linarith) h2 (by positivity) (by linarith)

/-- `RoomIsWithinTheBoundFrom`, with C₀ = 2c + 3. -/
theorem roomIsWithinTheBoundFrom : RoomIsWithinTheBoundFrom := by
  intro hL hBl hLv hEF hA c
  refine ⟨2 * c + 3, fun ρ x₀ l lam B h1 h2 h3 h4 h5 h6 h7 => ?_⟩
  have hN : Numbers ρ c x₀ lam B := ⟨h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨j, hj, hmax⟩ := Finset.exists_mem_eq_sup (range (l + 1)) ⟨0, mem_range.2 (by omega)⟩ fun j => lamAt ρ c x₀ l lam B j
  have hjl : j ≤ l := by have := mem_range.1 hj; omega
  have e1 : lamMax ρ c x₀ l lam B = lamAt ρ c x₀ l lam B j := hmax
  rw [e1]
  refine le_trans ?_ (levelBound_le_top hL hBl hEF hN (by omega : 2 * (c + 1) ≤ 2 * c + 3) l (l - j) j (by omega))
  obtain ⟨hΛ, hBB⟩ := pos_of_chainLabel hL hN hjl
  obtain ⟨Λ, hΛd⟩ : ∃ Λ : ℕ, Λ = lamAt ρ c x₀ l lam B j := ⟨_, rfl⟩
  obtain ⟨X, hXd⟩ : ∃ X : ℕ, X = baseAt ρ c x₀ l lam B j := ⟨_, rfl⟩
  have hK8 : 8 ≤ K x₀ j := by
    have a : 2 ^ 3 ≤ 2 ^ x₀ := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := two_pow_le_K x₀ j
    omega
  have hXK : K x₀ j * (Λ + 1) ≤ X := by rw [hXd, hΛd]; exact Nat.mul_le_mul_left _ (by omega)
  have hX2 : 2 * Λ ≤ X := by
    have : 2 * (Λ + 1) ≤ K x₀ j * (Λ + 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  have hX8 : 8 ≤ X := by
    have : 8 * 1 ≤ K x₀ j * (Λ + 1) := Nat.mul_le_mul hK8 (by omega)
    omega
  have r1 : PiecesCounted.room c Λ ≤ 2 ^ (c * Λ) * X ^ (2 * c + 3) := room_le_aux (Nat.pow_le_pow_left hX2 c) hX8 h3 Nat.one_le_two_pow
  have r2 : (PiecesCounted.room c Λ : ℝ) ≤ (2 : ℝ) ^ (c * Λ) * (X : ℝ) ^ (2 * c + 3) := by exact_mod_cast r1
  rw [← hΛd]
  refine r2.trans ?_
  unfold levelBound timeBound
  rw [baseAt_cast, ← hXd, ← hΛd]
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (by omega : 1 ≤ X)
  have hKsq : 1 ≤ K x₀ j ^ 2 := Nat.pow_pos (by omega)
  refine mul_le_mul ?_ (pow_le_pow_right₀ hX1 (Nat.le_mul_of_pos_right _ hKsq)) (by positivity) (by positivity)
  rw [← Real.rpow_natCast (2 : ℝ) (c * Λ)]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  push_cast
  exact mul_le_mul_of_nonneg_right (c_le_e_mul hLv hA hN j) (Nat.cast_nonneg _)

/-- `RoomIsWithinTheBound`. -/
theorem roomIsWithinTheBound : RoomIsWithinTheBound := roomIsWithinTheBoundFrom chainLabel boundBelow chainLevels exponentFits partAPrinted

end ExplicitCost
