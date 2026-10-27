/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Paper.SecCrossing_Crossing
public import PaddedDescent.F.Fuel
public import SingleBitPieces.SecCrossing_PolyA
public import ToTuring.Lib.Table
public import SingleBitPieces.SecNetworks_LemGrouping
public import Paper.SecLevel_Recursion
public import ClauseBound.Alg.Grid
import Mathlib.Tactic

/-! # The arithmetic of the cost of a level: the sizes [This file works with a form of Lemma 2 whose pieces differ from those the paper prints, with ρ = (log 12)/4 in place of the paper's ρ = 11/12.]

Section 5 of the paper, proof of Proposition 3, «Cost». `level_size`: the sizes that occur in the
loop over the terms add up to a polynomial in sc + B + λ; the paper counts operations only and has
no such bound. -/

public section

namespace SingleBitPieces.Level

open Groundwork

namespace Arith

end Arith

open Arith

/-- Section 5, proof of Proposition 3, «Cost», the sizes: the sum of the sizes that occur in the
loop over the terms is polynomial in sc + B + λ. Not in the paper, which counts operations only. -/
theorem level_size (g a A Rn : ℕ) : ∃ A2 : ℕ, ∀ sc B lam M P B' : ℕ, 1 ≤ lam → M ≤ 2 * Rn * lam → P ≤ g ^ 3 * lam →
    B' ≤ (g + 2 * g ^ 2) * (B + lam) →
    2 * sc + 2 * M + g * (P + B') + g * g * B' + 20 + a * (sc + B + lam) ^ a + A * (sc + (M + 1) + P + B') ^ A
      ≤ A2 * (sc + B + lam) ^ A2 := by
  obtain ⟨c1, hc1⟩ : ∃ c1 : ℕ, c1 = 22 + 4 * Rn + g * (2 * g ^ 3 + (g + 2 * g ^ 2)) + g * g * (g + 2 * g ^ 2) := ⟨_, rfl⟩
  obtain ⟨c3, hc3⟩ : ∃ c3 : ℕ, c3 = 2 + 2 * Rn + (2 * g ^ 3 + (g + 2 * g ^ 2)) := ⟨_, rfl⟩
  obtain ⟨A2, hA2⟩ : ∃ A2 : ℕ, A2 = c1 + a + A * c3 ^ A + a + A + 1 := ⟨_, rfl⟩
  refine ⟨A2, fun sc B lam M P B' hlam hM hP hB' => ?_⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : ℕ, Z = sc + B + lam := ⟨_, rfl⟩
  rw [← hZ]
  have hZ1 : 1 ≤ Z := by omega
  have hMZ : M ≤ 2 * Rn * Z := hM.trans (Nat.mul_le_mul_left _ (by omega))
  have hPZ : P ≤ 2 * g ^ 3 * Z := by
    have h3 : g ^ 3 * lam ≤ g ^ 3 * Z := Nat.mul_le_mul_left _ (by omega)
    have e3 : 2 * g ^ 3 * Z = g ^ 3 * Z + g ^ 3 * Z := by ring
    omega
  have hBZ : B' ≤ (g + 2 * g ^ 2) * Z := hB'.trans (Nat.mul_le_mul_left _ (by omega))
  have hPB : P + B' ≤ (2 * g ^ 3 + (g + 2 * g ^ 2)) * Z := by
    have e : (2 * g ^ 3 + (g + 2 * g ^ 2)) * Z = 2 * g ^ 3 * Z + (g + 2 * g ^ 2) * Z := by ring
    omega
  have h1 : g * (P + B') ≤ g * ((2 * g ^ 3 + (g + 2 * g ^ 2)) * Z) := Nat.mul_le_mul_left _ hPB
  have h2 : g * g * B' ≤ g * g * ((g + 2 * g ^ 2) * Z) := Nat.mul_le_mul_left _ hBZ
  have lin : 2 * sc + 2 * M + g * (P + B') + g * g * B' + 20 ≤ c1 * Z := by
    have e3 : c1 * Z = 22 * Z + 2 * (2 * Rn * Z) + g * ((2 * g ^ 3 + (g + 2 * g ^ 2)) * Z) + g * g * ((g + 2 * g ^ 2) * Z) := by
      rw [hc1]; ring
    omega
  have p2 : sc + (M + 1) + P + B' ≤ c3 * Z := by
    have e3 : c3 * Z = 2 * Z + 2 * Rn * Z + (2 * g ^ 3 + (g + 2 * g ^ 2)) * Z := by rw [hc3]; ring
    omega
  have q0 : Z ≤ Z ^ A2 := Nat.le_self_pow (by omega) Z
  have q1 : Z ^ a ≤ Z ^ A2 := Nat.pow_le_pow_right hZ1 (by omega)
  have q2 : (sc + (M + 1) + P + B') ^ A ≤ c3 ^ A * Z ^ A2 :=
    ((Nat.pow_le_pow_left p2 A).trans (le_of_eq (Nat.mul_pow ..))).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hZ1 (by omega)))
  have r0 : c1 * Z ≤ c1 * Z ^ A2 := Nat.mul_le_mul_left _ q0
  have r1 : a * Z ^ a ≤ a * Z ^ A2 := Nat.mul_le_mul_left _ q1
  have r2 : A * (sc + (M + 1) + P + B') ^ A ≤ A * c3 ^ A * Z ^ A2 := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ q2
  generalize Z ^ A2 = W at r0 r1 r2 ⊢
  have e : A2 * W = c1 * W + a * W + A * c3 ^ A * W + (a + A + 1) * W := by
    rw [hA2]
    ring
  omega

end SingleBitPieces.Level
