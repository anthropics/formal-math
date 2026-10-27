/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Suffices.Defs
import StepMachines.Math.SatArith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # «so the total time is O(2^{δn})»

The last sentence of the proof of Theorem 2: «Lemma 4 yields at most 2^{δn/3} such formulas, in time
2^{δn/3} times a polynomial in n, … so the total time is O(2^{δn}).»
With E = 2^{δn/3}: there are at most E formulas; each costs at most A·E plus A(n+1)^A plus 3 steps,
and (n+1)^A is at most a constant times E, so one formula costs at most a constant times E; the
remaining term D·n + 2 of the count is again at most a constant times E. The sum is at most a
constant times E³ = 2^{δn}. That a polynomial is O(2^{δn/3}) is `Groundwork.SatNet.pow_le_two_rpow`. -/

public section

namespace Suffices

/-- **«Lemma 4 yields at most 2^{δn/3} such formulas, in time 2^{δn/3} times a polynomial in n, … so
the total time is O(2^{δn})»** (proof of Theorem 2). -/
theorem stTotal : StTotal := by
  intro δ A D hδ
  obtain ⟨C, hC⟩ := Groundwork.SatNet.pow_le_two_rpow A (c := δ / 3) (by positivity)
  obtain ⟨C₁, hC₁⟩ := Groundwork.SatNet.pow_le_two_rpow 1 (c := δ / 3) (by positivity)
  obtain ⟨G, hG⟩ : ∃ G : ℕ, (2 : ℝ) ^ (δ / 3) ≤ G := ⟨⌈(2 : ℝ) ^ (δ / 3)⌉₊, Nat.le_ceil _⟩
  refine ⟨A + A * C * G + 3 + D * C₁ + 2, fun n N x hN hx => ?_⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (2 : ℝ) ^ (δ / 3 * n) := ⟨_, rfl⟩
  have hx' : (2 : ℝ) ^ x ≤ E := by rw [hE]; exact Real.rpow_le_rpow_of_exponent_le one_le_two hx
  have hE1 : 1 ≤ E := by rw [hE]; exact Real.one_le_rpow one_le_two (by positivity)
  have hE0 : 0 ≤ E := by linarith
  have hE3 : (2 : ℝ) ^ (δ * n) = E * E * E := by
    rw [hE, ← Real.rpow_add two_pos, ← Real.rpow_add two_pos]
    congr 1; ring
  have hA0 : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg A
  have hC0 : (0 : ℝ) ≤ (C : ℝ) := Nat.cast_nonneg C
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg D
  have hC10 : (0 : ℝ) ≤ (C₁ : ℝ) := Nat.cast_nonneg C₁
  have hG0 : (0 : ℝ) ≤ (G : ℝ) := Nat.cast_nonneg G
  -- a polynomial in n is O(2^{δn/3})
  have hp : ((n : ℝ) + 1) ^ A ≤ C * G * E := by
    have h := hC (n + 1)
    push_cast at h
    calc ((n : ℝ) + 1) ^ A ≤ C * (2 : ℝ) ^ (δ / 3 * ((n : ℝ) + 1)) := h
      _ = C * ((2 : ℝ) ^ (δ / 3) * E) := by rw [hE, ← Real.rpow_add two_pos]; congr 2; ring
      _ ≤ C * (G * E) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hG hE0) hC0
      _ = C * G * E := by ring
  have hn : (n : ℝ) ≤ C₁ * E := by
    have h := hC₁ n
    rwa [pow_one, ← hE] at h
  rw [← hE] at hN
  -- the cost of one formula
  have t1 : (A : ℝ) * (2 : ℝ) ^ x + A * ((n : ℝ) + 1) ^ A + 3 ≤ (A + A * C * G + 3) * E := by
    have u1 := mul_le_mul_of_nonneg_left hx' hA0
    have u2 := mul_le_mul_of_nonneg_left hp hA0
    calc (A : ℝ) * (2 : ℝ) ^ x + A * ((n : ℝ) + 1) ^ A + 3 ≤ A * E + A * (C * G * E) + 3 * E := by linarith
      _ = (A + A * C * G + 3) * E := by ring
  -- all formulas
  have t2 : (N : ℝ) * ((A : ℝ) * (2 : ℝ) ^ x + A * ((n : ℝ) + 1) ^ A + 3) ≤ E * ((A + A * C * G + 3) * E) := mul_le_mul hN t1 (by positivity) hE0
  -- the enumeration
  have t3 : (D : ℝ) * n ≤ D * (C₁ * E) := mul_le_mul_of_nonneg_left hn hD0
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = E * E * E := ⟨_, rfl⟩
  have hEE : E ≤ E * E := by nlinarith
  have hEP : E * E ≤ P := by rw [hP]; nlinarith [mul_nonneg hE0 hE0]
  have k1 : ((A : ℝ) + A * C * G + 3) * (E * E) ≤ (A + A * C * G + 3) * P := mul_le_mul_of_nonneg_left hEP (by positivity)
  have k2 : (D : ℝ) * C₁ * E ≤ D * C₁ * P := mul_le_mul_of_nonneg_left (hEE.trans hEP) (by positivity)
  have k3 : (1 : ℝ) ≤ P := hE1.trans (hEE.trans hEP)
  rw [hE3, ← hP]
  push_cast
  calc (N : ℝ) * ((A : ℝ) * (2 : ℝ) ^ x + A * ((n : ℝ) + 1) ^ A + 3) + D * n + 2
      ≤ E * ((A + A * C * G + 3) * E) + D * (C₁ * E) + 2 := by linarith
    _ = (A + A * C * G + 3) * (E * E) + D * C₁ * E + 2 := by ring
    _ ≤ (A + A * C * G + 3) * P + D * C₁ * P + 2 * P := by linarith
    _ = (A + A * C * G + 3 + D * C₁ + 2) * P := by ring

end Suffices
