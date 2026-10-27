/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.Chain
import Mathlib.Tactic

/-! # The sizes of the states of the tower

The paper bounds no memory. With X_j = K_j(Λ_j + 𝔅_j): X_j ≤ X_{j+1}^{c+5} (`ChainBase`), so X_j ≤
X_ℓ^{(c+5)^{ℓ−j}} ≤ X_ℓ^{K_ℓ} by (c + 5)^ℓ ≤ K_ℓ (`ChainLevels`).
So ∑_{j≤ℓ} X_j^C ≤ (ℓ + 1)·X_ℓ^{CK_ℓ}, and the bound `Tower.towerSize`, a polynomial of degree 3 in
ℓ times that, is at most X_ℓ^{(C+6)K_ℓ}, since ℓ + 3 ≤ X_ℓ. Natural numbers only, up to the last
line. -/

public section

namespace ExplicitCost

open Levels.Gen Printed QueryMachines Finset

/-- The bound for the tower from a bound for its parts: R ≤ mY with ℓ + 3 = m and Y ≥ 1 gives at
most 5m³Y. -/
theorem towerSize_le {l R m Y : ℕ} (hm : m = l + 3) (hY : 1 ≤ Y) (hR : R ≤ m * Y) : Tower.towerSize l R R R ≤ 5 * (m ^ 3 * Y) := by
  have a0 : 1 ≤ m * Y := Nat.mul_pos (by omega) hY
  have a1 : l * (R + 1) + R + R + 3 ≤ m * (R + 1) := by
    have : m * (R + 1) = l * (R + 1) + 3 * (R + 1) := by rw [hm]; ring
    omega
  have a2 : R + 1 ≤ 2 * (m * Y) := by omega
  have a3 : (2 * l + 2) * (l * (R + 1) + R + R + 3) ≤ (2 * m) * (m * (2 * (m * Y))) := Nat.mul_le_mul (by omega) (a1.trans (Nat.mul_le_mul_left _ a2))
  have a4 : (2 * m) * (m * (2 * (m * Y))) = 4 * (m ^ 3 * Y) := by ring
  have a5 : 1 ≤ m ^ 3 * Y := Nat.mul_pos (Nat.pow_pos (by omega)) hY
  unfold Tower.towerSize
  omega

/-- `TotalRoomFrom`, with C₀ = C + 6. -/
theorem totalRoomFrom : TotalRoomFrom := by
  intro hB hLv c C
  refine ⟨C + 6, fun ρ x₀ l lam B h1 h2 h3 h4 h5 h6 h7 => ?_⟩
  have hN : Numbers ρ c x₀ lam B := ⟨h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨X, hX⟩ : ∃ X, X = K x₀ l * (lam + B) := ⟨_, rfl⟩
  have hXl : baseAt ρ c x₀ l lam B l = X := by rw [hX, baseAt, lamAt_self, bitsAt_self]
  have hKl := (hLv c x₀ l 0 h4 h5 (Nat.zero_le l)).2
  have hK3 : 3 ≤ K x₀ l := by
    have a : 2 ^ 2 ≤ 2 ^ x₀ := Nat.pow_le_pow_right (by norm_num) (by omega)
    have := two_pow_le_K x₀ l
    omega
  have hlK : l < K x₀ l := (Nat.lt_two_pow_self (n := l)).trans_le ((Nat.pow_le_pow_left (by omega) l).trans hKl)
  have h2K : K x₀ l * 2 ≤ X := by rw [hX]; exact Nat.mul_le_mul_left _ (by omega)
  have hX1 : 1 ≤ X := by omega
  -- X_j ≤ X^{(c+5)^{ℓ−j}}
  have s1 : ∀ k j, j + k = l → baseAt ρ c x₀ l lam B j ≤ X ^ (c + 5) ^ k := by
    intro k
    induction k with
    | zero =>
      intro j hj
      obtain rfl : j = l := by omega
      rw [hXl]
      simp
    | succ k ih =>
      intro j hj
      calc baseAt ρ c x₀ l lam B j ≤ baseAt ρ c x₀ l lam B (j + 1) ^ (c + 5) := hB ρ c x₀ l lam B j hN (by omega)
        _ ≤ (X ^ (c + 5) ^ k) ^ (c + 5) := Nat.pow_le_pow_left (ih (j + 1) (by omega)) _
        _ = X ^ (c + 5) ^ (k + 1) := by rw [← pow_mul, pow_succ]
  -- X_j^C ≤ X^{CK_ℓ}
  have s2 : ∀ j ∈ range (l + 1), (K x₀ j * (lamAt ρ c x₀ l lam B j + bitsAt ρ c x₀ l lam B j)) ^ C ≤ X ^ (C * K x₀ l) := by
    intro j hj
    have hjl : j ≤ l := by have := mem_range.1 hj; omega
    have a1 : (c + 5) ^ (l - j) ≤ K x₀ l := (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)).trans hKl
    calc (K x₀ j * (lamAt ρ c x₀ l lam B j + bitsAt ρ c x₀ l lam B j)) ^ C ≤ (X ^ (c + 5) ^ (l - j)) ^ C := Nat.pow_le_pow_left (s1 (l - j) j (by omega)) _
      _ ≤ (X ^ K x₀ l) ^ C := Nat.pow_le_pow_left (Nat.pow_le_pow_right hX1 a1) _
      _ = X ^ (C * K x₀ l) := by rw [← pow_mul, Nat.mul_comm]
  have s3 : roomAll C ρ c x₀ l lam B ≤ (l + 3) * X ^ (C * K x₀ l) := by
    have := Finset.sum_le_card_nsmul _ _ _ s2
    rw [card_range, smul_eq_mul] at this
    exact this.trans (Nat.mul_le_mul_right _ (by omega))
  have s4 := towerSize_le (l := l) rfl (Nat.pow_pos hX1) s3
  have s5 : 5 * ((l + 3) ^ 3 * X ^ (C * K x₀ l)) ≤ X ^ ((C + 6) * K x₀ l) := by
    have b1 : (l + 3) ^ 3 ≤ X ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have b2 : 5 ≤ X ^ 3 := by
      have : 2 ^ 3 ≤ X ^ 3 := Nat.pow_le_pow_left (by omega) 3
      omega
    calc 5 * ((l + 3) ^ 3 * X ^ (C * K x₀ l)) ≤ X ^ 3 * (X ^ 3 * X ^ (C * K x₀ l)) := Nat.mul_le_mul b2 (Nat.mul_le_mul_right _ b1)
      _ = X ^ (6 + C * K x₀ l) := by ring
      _ ≤ X ^ ((C + 6) * K x₀ l) := Nat.pow_le_pow_right hX1 (by
          have : (C + 6) * K x₀ l = C * K x₀ l + 6 * K x₀ l := by ring
          omega)
  have s6 := s4.trans s5
  unfold sizeBound
  rw [hX] at s6
  exact_mod_cast s6

/-- `TotalRoom`. -/
theorem totalRoom : TotalRoom := totalRoomFrom chainBase chainLevels

end ExplicitCost
