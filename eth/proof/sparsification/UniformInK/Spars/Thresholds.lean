/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import UniformInK.Spars.Defs
import Mathlib.Tactic.Ring

/-! # The thresholds θ 0 = 1 and θ i = 4·τ^(2i−1) for i ≥ 1

This file proves `StThrU` and `StBetaSumU`. Here β 0 = 0 and β i = 4·τ^(2i−2) for i ≥ 1, so the term
i' = 0 of the sum vanishes and every product 2·θ(i−i')·β i' with 1 ≤ i' < i equals 32·τ^(2i−3);
so for i ≥ 2 the left-hand side of `ThrU.step` is (32i − 16)·τ^(2i−3), which is at most β i =
4·τ^(2i−2) as soon as 8i − 4 ≤ τ. -/

public section

namespace UniformInK

open Finset

namespace Thresholds

/-- The thresholds are positive, if τ is. -/
theorem thetaU_pos {τ : ℕ} (hτ : 0 < τ) (i : ℕ) : 0 < thetaU τ i := by
  cases i with
  | zero => exact Nat.one_pos
  | succ i => exact Nat.mul_pos (by omega) (Nat.pow_pos hτ)

/-- τ·β r ≤ θ r. -/
theorem mul_betaSU_le (τ r : ℕ) : τ * betaSU τ r ≤ thetaU τ r := by
  cases r with
  | zero => simp [betaSU]
  | succ r => exact le_of_eq (by simp only [betaSU, thetaU]; ring)

/-- One product in `ThrU.step`: 2·θ(i+1−j)·β(j+1) = 32·τ^(2i+1) for j ≤ i. -/
theorem term_eq (τ : ℕ) {i j : ℕ} (hj : j ≤ i) : 2 * thetaU τ (i + 2 - (j + 1)) * betaSU τ (j + 1) = 32 * τ ^ (2 * i + 1) := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hj
  have h : j + c + 2 - (j + 1) = c + 1 := by omega
  rw [h]
  simp only [betaSU, thetaU]
  ring

/-- The sum in `ThrU.step` at i + 2 equals 32·(i+1)·τ^(2i+1). -/
theorem sum_eq (τ i : ℕ) : ∑ i' ∈ range (i + 2), 2 * thetaU τ (i + 2 - i') * betaSU τ i' = 32 * (i + 1) * τ ^ (2 * i + 1) := by
  rw [sum_range_succ', sum_congr rfl fun j hj => term_eq τ (Nat.lt_succ_iff.1 (mem_range.1 hj)), sum_const, card_range, smul_eq_mul]
  simp only [betaSU, Nat.succ_eq_add_one]
  ring

/-- `ThrU.step` for the thresholds `thetaU τ` and the bounds `betaSU τ`, if 8i ≤ τ + 4. -/
theorem step_le {τ i : ℕ} (hi : 0 < i) (hτ : 8 * i ≤ τ + 4) :
    4 * thetaU τ (i - 1) + ∑ i' ∈ range i, 2 * thetaU τ (i - i') * betaSU τ i' ≤ betaSU τ i := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
  cases i with
  | zero => simp [betaSU, thetaU]
  | succ i =>
    rw [sum_eq]
    have h : i + 1 + 1 - 1 = i + 1 := rfl
    rw [h]
    simp only [betaSU, thetaU]
    calc 4 * (4 * τ ^ (2 * i + 1)) + 32 * (i + 1) * τ ^ (2 * i + 1) = 4 * ((8 * i + 12) * τ ^ (2 * i + 1)) := by ring
      _ ≤ 4 * (τ * τ ^ (2 * i + 1)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
      _ = 4 * τ ^ (2 * (i + 1)) := by ring

/-- β k ≤ τ^(2k), if 2 ≤ τ. -/
theorem betaSU_le {τ : ℕ} (hτ : 2 ≤ τ) (k : ℕ) : betaSU τ k ≤ τ ^ (2 * k) := by
  cases k with
  | zero => simp [betaSU]
  | succ k =>
    simp only [betaSU]
    calc 4 * τ ^ (2 * k) ≤ τ * τ * τ ^ (2 * k) := Nat.mul_le_mul_right _ (Nat.mul_le_mul hτ hτ)
      _ = τ ^ (2 * (k + 1)) := by ring

end Thresholds

/-- The thresholds `thetaU τ` and the bounds `betaSU τ` have the three properties for width k, if 1
≤ k and 8k ≤ τ. -/
theorem stThrU : StThrU := fun k τ hk hτ =>
  { pos := Thresholds.thetaU_pos (by omega)
    step := fun _ hi hik => Thresholds.step_le hi (by omega)
    mul := Thresholds.mul_betaSU_le τ }

/-- β 0 + … + β (k-1) is at most τ^(2k), if 2 ≤ τ. -/
theorem stBetaSumU : StBetaSumU := by
  intro τ k hτ
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, bsumU]
    rw [bsumU] at ih
    calc ∑ i ∈ range k, betaSU τ i + betaSU τ k ≤ τ ^ (2 * k) + τ ^ (2 * k) := Nat.add_le_add ih (Thresholds.betaSU_le hτ k)
      _ = 2 * 1 * τ ^ (2 * k) := by ring
      _ ≤ τ * τ * τ ^ (2 * k) := Nat.mul_le_mul_right _ (Nat.mul_le_mul hτ (by omega))
      _ = τ ^ (2 * (k + 1)) := by ring

end UniformInK
