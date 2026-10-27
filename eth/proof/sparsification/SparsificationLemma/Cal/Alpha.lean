/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsificationLemma.Cal.Defs
import SparsificationLemma.Cal.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # The numbers x = 32(k−1)²/ε and α = ⌈2(k−1)²·ε⁻¹·⌈log₂ x⌉⌉

This file proves `StAlpha`, `StAlphaLe` and `StDegLe`, and that `logC` is ⌈log₂ x⌉.
For a rational x ≥ 1 the least natural number m with ⌈x⌉ ≤ 2^m is ⌈log₂ x⌉, because x ≤ 2^m, ⌈x⌉ ≤
2^m and log₂ x ≤ m say the same.
`StAlpha`: 2(k−1)²/ε = x/16, so x·⌈log₂ x⌉/16 ≤ α < x·⌈log₂ x⌉/16 + 1; and x ≥ 128 gives ⌈log₂ x⌉ ≥ 7.
`StAlphaLe`: the chain 32α ≤ 2x·⌈log₂ x⌉ + 32 ≤ 2·x^(3/2) ≤ 363·k³·ε^(−3/2) ≤ (8k/ε)³, in three
theorems: `alphaC_le_sqrt` has the first two links, `sqrt_xC_le` the third, `div_sqrt_le_cube` the
last. The second link is 2x·(log₂ x + 1 + 16/x) ≤ 2x·√x, by `StSqrt`.
We write x·√x for x^(3/2) and ε·√ε for ε^(3/2).
`StDegLe`: 2 + 4α·(32α)^(k−2) ≤ (32α)^(k−1) ≤ ((8k/ε)³)^(k−1) ≤ (8k/ε)^(3k). -/

public section

namespace SparsificationLemma.Cal

/-- For a rational x > 0: log₂ x ≤ `Nat.clog 2 ⌈x⌉₊`. -/
theorem logb_le_clog {x : ℚ} (hx : 0 < x) : Real.logb 2 (x : ℝ) ≤ (Nat.clog 2 ⌈x⌉₊ : ℝ) := by
  have hx' : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  rw [Real.logb_le_iff_le_rpow (by norm_num) hx', Real.rpow_natCast]
  have h1 : x ≤ (⌈x⌉₊ : ℚ) := Nat.le_ceil x
  have h2 : ⌈x⌉₊ ≤ 2 ^ Nat.clog 2 ⌈x⌉₊ := Nat.le_pow_clog (by norm_num) _
  have h3 : x ≤ ((2 ^ Nat.clog 2 ⌈x⌉₊ : ℕ) : ℚ) := h1.trans (by exact_mod_cast h2)
  have h4 : (x : ℝ) ≤ (((2 ^ Nat.clog 2 ⌈x⌉₊ : ℕ) : ℚ) : ℝ) := by exact_mod_cast h3
  simpa using h4

/-- For a rational x ≥ 1: `Nat.clog 2 ⌈x⌉₊` < log₂ x + 1. -/
theorem clog_lt_logb_add_one {x : ℚ} (hx : 1 ≤ x) : (Nat.clog 2 ⌈x⌉₊ : ℝ) < Real.logb 2 (x : ℝ) + 1 := by
  have hx' : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have h0 : 0 ≤ Real.logb 2 (x : ℝ) := Real.logb_nonneg (by norm_num) hx'
  rcases Nat.eq_zero_or_pos (Nat.clog 2 ⌈x⌉₊) with h | h
  · rw [h]; push_cast; linarith
  · obtain ⟨m, hm⟩ : ∃ m, Nat.clog 2 ⌈x⌉₊ = m + 1 := ⟨Nat.clog 2 ⌈x⌉₊ - 1, by omega⟩
    have h1 : 2 ^ m < ⌈x⌉₊ := Nat.pow_lt_of_lt_clog (by omega)
    have h2 : ((2 ^ m : ℕ) : ℚ) < x := Nat.lt_ceil.mp h1
    have h3 : (((2 ^ m : ℕ) : ℚ) : ℝ) < (x : ℝ) := by exact_mod_cast h2
    have h4 : (m : ℝ) < Real.logb 2 (x : ℝ) := by
      rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by linarith), Real.rpow_natCast]
      simpa using h3
    rw [hm]; push_cast; linarith

/-- For a rational x ≥ 1: `Nat.clog 2 ⌈x⌉₊` = ⌈log₂ x⌉. -/
theorem clog_eq_ceil_logb {x : ℚ} (hx : 1 ≤ x) : ((Nat.clog 2 ⌈x⌉₊ : ℕ) : ℤ) = ⌈Real.logb 2 (x : ℝ)⌉ := by
  symm
  rw [Int.ceil_eq_iff]
  have h1 := logb_le_clog (lt_of_lt_of_le one_pos hx)
  have h2 := clog_lt_logb_add_one hx
  constructor
  · push_cast; linarith
  · push_cast; exact h1

/-- x ≥ 32 for k ≥ 2 and ε ∈ (0,1]. -/
theorem le_xC_of_two_le {k : ℕ} {ε : ℚ} (hk : 2 ≤ k) (h0 : 0 < ε) (h1 : ε ≤ 1) : 32 ≤ xC k ε := by
  have hk' : (2 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
  rw [xC, le_div_iff₀ h0]
  nlinarith

/-- x ≥ 128 for k ≥ 3 and ε ∈ (0,1]. -/
theorem le_xC {k : ℕ} {ε : ℚ} (hk : 3 ≤ k) (h0 : 0 < ε) (h1 : ε ≤ 1) : 128 ≤ xC k ε := by
  have hk' : (3 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
  rw [xC, le_div_iff₀ h0]
  nlinarith

/-- `logC` is ⌈log₂ x⌉, for k ≥ 2 and ε ∈ (0,1]. -/
theorem stLogC : StLogC := by
  intro k ε hk h0 h1
  exact clog_eq_ceil_logb (by linarith [le_xC_of_two_le hk h0 h1])

/-- What the sparsification uses of x and α: x ≥ 128, α ≥ 2, α ≥ k², 32α ≥ 2x·log₂ x, 32α ≤ 2x·⌈log₂
x⌉ + 32. -/
theorem stAlpha : StAlpha := by
  intro k ε hk h0 h1
  have hk' : (3 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
  have hx := le_xC hk h0 h1
  have hx0 : 0 < xC k ε := by linarith
  have hxR : (128 : ℝ) ≤ ((xC k ε : ℚ) : ℝ) := by exact_mod_cast hx
  have hlog : Real.logb 2 ((xC k ε : ℚ) : ℝ) ≤ (logC k ε : ℝ) := logb_le_clog hx0
  have h7R : (7 : ℝ) ≤ (logC k ε : ℝ) := (seven_le_logb hxR).trans hlog
  have h7 : (7 : ℚ) ≤ (logC k ε : ℚ) := by exact_mod_cast h7R
  have hu : 2 * ((k : ℚ) - 1) ^ 2 / ε * (logC k ε : ℚ) = xC k ε / 16 * (logC k ε : ℚ) := by
    rw [xC]; ring
  have hlo : xC k ε / 16 * (logC k ε : ℚ) ≤ (alphaC k ε : ℚ) := by
    rw [← hu]; exact Nat.le_ceil _
  have hhi : (alphaC k ε : ℚ) < xC k ε / 16 * (logC k ε : ℚ) + 1 := by
    rw [← hu]; exact Nat.ceil_lt_add_one (by positivity)
  have hxk : 32 * ((k : ℚ) - 1) ^ 2 ≤ xC k ε := by
    rw [xC, le_div_iff₀ h0]
    have : 0 ≤ ((k : ℚ) - 1) ^ 2 := by positivity
    nlinarith
  have hprod : 7 * xC k ε ≤ xC k ε * (logC k ε : ℚ) := by nlinarith
  have hk2 : ((k ^ 2 : ℕ) : ℚ) ≤ (alphaC k ε : ℚ) := by push_cast; nlinarith
  refine ⟨hx, ?_, by exact_mod_cast hk2, ?_, by linarith⟩
  · have : (2 : ℚ) ≤ (alphaC k ε : ℚ) := by linarith
    exact_mod_cast this
  · have hloR : ((xC k ε : ℚ) : ℝ) / 16 * (logC k ε : ℝ) ≤ (alphaC k ε : ℝ) := by exact_mod_cast hlo
    have : ((xC k ε : ℚ) : ℝ) * Real.logb 2 ((xC k ε : ℚ) : ℝ) ≤ ((xC k ε : ℚ) : ℝ) * (logC k ε : ℝ) :=
      mul_le_mul_of_nonneg_left hlog (by linarith)
    linarith

/-- x as a real number. -/
theorem xC_cast (k : ℕ) (ε : ℚ) : ((xC k ε : ℚ) : ℝ) = 32 * ((k : ℝ) - 1) ^ 2 / (ε : ℝ) := by
  rw [xC]; push_cast; ring

/-- 32α ≤ 2x·⌈log₂ x⌉ + 32 ≤ 2·x^(3/2), written 2·x·√x. -/
theorem alphaC_le_sqrt {k : ℕ} {ε : ℚ} (hk : 3 ≤ k) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    32 * (alphaC k ε : ℝ) ≤ 2 * ((xC k ε : ℚ) : ℝ) * Real.sqrt ((xC k ε : ℚ) : ℝ) := by
  obtain ⟨hx, -, -, -, hhi⟩ := stAlpha k ε hk h0 h1
  have hxR : (128 : ℝ) ≤ ((xC k ε : ℚ) : ℝ) := by exact_mod_cast hx
  have hhiR : 32 * (alphaC k ε : ℝ) ≤ 2 * ((xC k ε : ℚ) : ℝ) * (logC k ε : ℝ) + 32 := by exact_mod_cast hhi
  have hlt : (logC k ε : ℝ) < Real.logb 2 ((xC k ε : ℚ) : ℝ) + 1 := clog_lt_logb_add_one (by linarith)
  have hsq := stSqrt _ hxR
  generalize ((xC k ε : ℚ) : ℝ) = x at *
  have hx0 : 0 < x := by linarith
  have h16 : x * (16 / x) = 16 := by field_simp
  nlinarith

/-- 2·x^(3/2) ≤ 363·k³·ε^(−3/2), written with x·√x and ε·√ε. It holds because √32 ≤ 5.66 and
2·32·5.66 ≤ 363. -/
theorem sqrt_xC_le {k : ℕ} {ε : ℚ} (hk : 3 ≤ k) (h0 : 0 < ε) :
    2 * ((xC k ε : ℚ) : ℝ) * Real.sqrt ((xC k ε : ℚ) : ℝ) ≤ 363 * (k : ℝ) ^ 3 / ((ε : ℝ) * Real.sqrt (ε : ℝ)) := by
  have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h0R : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast h0
  have hr0 : 0 < Real.sqrt (ε : ℝ) := Real.sqrt_pos.mpr h0R
  have hr2 : Real.sqrt (ε : ℝ) ^ 2 = (ε : ℝ) := Real.sq_sqrt h0R.le
  rw [xC_cast]
  have hx0 : 0 ≤ 32 * ((k : ℝ) - 1) ^ 2 / (ε : ℝ) := by positivity
  have hw : Real.sqrt (32 * ((k : ℝ) - 1) ^ 2 / (ε : ℝ)) ≤ 5.66 * ((k : ℝ) - 1) / Real.sqrt (ε : ℝ) := by
    rw [Real.sqrt_le_iff]
    refine ⟨div_nonneg (by linarith) hr0.le, ?_⟩
    rw [div_pow, hr2]
    apply div_le_div_of_nonneg_right _ h0R.le
    have : 0 ≤ ((k : ℝ) - 1) ^ 2 := by positivity
    nlinarith
  refine (mul_le_mul_of_nonneg_left hw (by linarith)).trans ?_
  have e1 : 2 * (32 * ((k : ℝ) - 1) ^ 2 / (ε : ℝ)) * (5.66 * ((k : ℝ) - 1) / Real.sqrt (ε : ℝ))
      = 362.24 * ((k : ℝ) - 1) ^ 3 / ((ε : ℝ) * Real.sqrt (ε : ℝ)) := by
    field_simp; ring
  rw [e1]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have c1 : ((k : ℝ) - 1) ^ 3 ≤ (k : ℝ) ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
  have c2 : 0 ≤ ((k : ℝ) - 1) ^ 3 := pow_nonneg (by linarith) 3
  nlinarith

/-- 363·k³·ε^(−3/2) ≤ (8k/ε)³ for ε ∈ (0,1], because ε³ ≤ ε·√ε and 363 ≤ 512. -/
theorem div_sqrt_le_cube (k : ℕ) {ε : ℚ} (h0 : 0 < ε) (h1 : ε ≤ 1) :
    363 * (k : ℝ) ^ 3 / ((ε : ℝ) * Real.sqrt (ε : ℝ)) ≤ (8 * (k : ℝ) / (ε : ℝ)) ^ 3 := by
  have h0R : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast h0
  have h1R : (ε : ℝ) ≤ 1 := by exact_mod_cast h1
  have hr0 : 0 < Real.sqrt (ε : ℝ) := Real.sqrt_pos.mpr h0R
  have hre : (ε : ℝ) ≤ Real.sqrt (ε : ℝ) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hk3 : 0 ≤ (k : ℝ) ^ 3 := by positivity
  have h3 : (ε : ℝ) ^ 3 ≤ (ε : ℝ) * Real.sqrt (ε : ℝ) := by
    have : (ε : ℝ) ^ 2 ≤ (ε : ℝ) := by nlinarith
    nlinarith
  rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left h3 hk3, mul_nonneg hk3 (mul_pos h0R hr0).le]

/-- 32α ≤ (8k/ε)³, for k ≥ 3 and ε ∈ (0,1]. -/
theorem stAlphaLe : StAlphaLe := fun k _ hk h0 h1 =>
  (alphaC_le_sqrt hk h0 h1).trans ((sqrt_xC_le hk h0).trans (div_sqrt_le_cube k h0 h1))

/-- 2 + 4α·(32α)^(k−2) ≤ (8k/ε)^(3k), for k ≥ 3 and ε ∈ (0,1]. -/
theorem stDegLe : StDegLe := by
  intro k ε hk h0 h1
  obtain ⟨-, hα, -, -, -⟩ := stAlpha k ε hk h0 h1
  have hle := stAlphaLe k ε hk h0 h1
  have hkR : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h0R : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast h0
  have h1R : (ε : ℝ) ≤ 1 := by exact_mod_cast h1
  have hB : 1 ≤ 8 * (k : ℝ) / (ε : ℝ) := by rw [le_div_iff₀ h0R]; linarith
  have hN : 2 + 4 * alphaC k ε * (32 * alphaC k ε) ^ (k - 2) ≤ (32 * alphaC k ε) ^ (k - 1) := by
    have hp : 1 ≤ (32 * alphaC k ε) ^ (k - 2) := Nat.one_le_pow _ _ (by omega)
    have he : (32 * alphaC k ε) ^ (k - 1) = 32 * alphaC k ε * (32 * alphaC k ε) ^ (k - 2) := by
      rw [show k - 1 = (k - 2) + 1 by omega, pow_succ]; ring
    rw [he]
    nlinarith
  calc ((2 + 4 * alphaC k ε * (32 * alphaC k ε) ^ (k - 2) : ℕ) : ℝ)
      ≤ (((32 * alphaC k ε) ^ (k - 1) : ℕ) : ℝ) := by exact_mod_cast hN
    _ = (32 * (alphaC k ε : ℝ)) ^ (k - 1) := by push_cast; ring
    _ ≤ ((8 * (k : ℝ) / (ε : ℝ)) ^ 3) ^ (k - 1) := pow_le_pow_left₀ (by positivity) hle _
    _ = (8 * (k : ℝ) / (ε : ℝ)) ^ (3 * (k - 1)) := by rw [← pow_mul]
    _ ≤ (8 * (k : ℝ) / (ε : ℝ)) ^ (3 * k) := pow_le_pow_right₀ hB (by omega)

end SparsificationLemma.Cal
