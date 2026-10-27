/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsificationLemma.Geo.Defs
import SparsificationLemma.Geo.Tau
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # The choice τ = ⌈(8k/ε)³⌉ in the sparsification, for a rational ε ∈ (0,1]

This file proves `StTauE`, with two lemmas on real numbers.
`StTauE`: put X = 8k/ε ≥ 8 and τ = ⌈X³⌉. Then X³ ≤ τ ≤ X³ + 1 ≤ (9X/8)³ = (9k/ε)³. So log₂ τ ≤
3·log₂(9X/8) ≤ 27X/8, because log₂ y ≤ y, and
log₂(e·τ·τ^(2k)) ≤ 2 + (2k+1)·27X/8 ≤ 11kX. Hence (k/τ)·log₂(e·τ·τ^(2k)) ≤ 11k²X/X³ = 11ε²/64 ≤ ε. -/

public section

namespace SparsificationLemma.Geo

open UniformInK

/-- ln y ≤ y·ln 2 for y > 0, that is log₂ y ≤ y. -/
theorem log_le_mul_log_two {y : ℝ} (hy : 0 < y) : Real.log y ≤ y * Real.log 2 := by
  have hL1 := Real.log_two_gt_d9
  have hL2 := Real.log_two_lt_d9
  have h1 : Real.log (y / 2) ≤ y / 2 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hy.ne' (by norm_num)] at h1
  nlinarith

/-- The inequality of `StTauE` between real numbers: (k/T)·log₂(e·T·T^(2k)) ≤ ε, if X = 8k/ε, k ≥ 1,
ε ∈ (0,1] and X³ ≤ T ≤ (9X/8)³. -/
theorem works_of_cube {k : ℕ} {ε X T : ℝ} (hk : 1 ≤ (k : ℝ)) (h0 : 0 < ε) (h1 : ε ≤ 1) (hX : (k : ℝ) = ε * X / 8)
    (hlo : X ^ 3 ≤ T) (hhi : T ≤ (9 * X / 8) ^ 3) :
    ((k : ℝ) / T) * Real.logb 2 (Real.exp 1 * T * T ^ (2 * k)) ≤ ε := by
  have hX8 : 8 ≤ X := by nlinarith
  have hX0 : 0 < X := by linarith
  have hX3 : 0 < X ^ 3 := by positivity
  have hT0 : 0 < T := by linarith
  have hL1 := Real.log_two_gt_d9
  have hL0 : 0 < Real.log 2 := by linarith
  have hlogT : Real.log T ≤ 27 * X / 8 * Real.log 2 := by
    have a1 : Real.log T ≤ Real.log ((9 * X / 8) ^ 3) := Real.log_le_log hT0 hhi
    rw [Real.log_pow] at a1
    have a2 := log_le_mul_log_two (y := 9 * X / 8) (by positivity)
    push_cast at a1
    linarith
  have hlog : Real.log (Real.exp 1 * T * T ^ (2 * k)) = 1 + (2 * (k : ℝ) + 1) * Real.log T := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (Real.exp_pos 1).ne' hT0.ne', Real.log_exp, Real.log_pow]
    push_cast; ring
  have hW : Real.logb 2 (Real.exp 1 * T * T ^ (2 * k)) ≤ 11 * (k : ℝ) * X := by
    rw [Real.logb, div_le_iff₀ hL0, hlog]
    have b1 : (2 * (k : ℝ) + 1) * Real.log T ≤ (2 * (k : ℝ) + 1) * (27 * X / 8 * Real.log 2) :=
      mul_le_mul_of_nonneg_left hlogT (by linarith)
    have b2 : 2 + (2 * (k : ℝ) + 1) * (27 * X / 8) ≤ 11 * (k : ℝ) * X := by nlinarith
    have b3 := mul_le_mul_of_nonneg_right b2 hL0.le
    nlinarith
  have hkT : 0 ≤ (k : ℝ) / T := by positivity
  refine (mul_le_mul_of_nonneg_left hW hkT).trans ?_
  rw [div_mul_eq_mul_div, div_le_iff₀ hT0]
  have c1 : (k : ℝ) * (11 * (k : ℝ) * X) = 11 / 64 * ε ^ 2 * X ^ 3 := by rw [hX]; ring
  rw [c1]
  have c2 : 11 / 64 * ε ^ 2 ≤ ε := by nlinarith
  calc 11 / 64 * ε ^ 2 * X ^ 3 ≤ ε * X ^ 3 := mul_le_mul_of_nonneg_right c2 hX3.le
    _ ≤ ε * T := mul_le_mul_of_nonneg_left hlo h0.le

/-- τ = ⌈(8k/ε)³⌉ is large enough for k and ε, and at most (9k/ε)³. -/
theorem stTauE : StTauE := by
  intro k ε hk h0 h1
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have h0R : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast h0
  have h1R : (ε : ℝ) ≤ 1 := by exact_mod_cast h1
  have hq0 : 0 ≤ (8 * (k : ℚ) / ε) ^ 3 := by positivity
  have hloQ : (8 * (k : ℚ) / ε) ^ 3 ≤ (tauE k ε : ℚ) := Nat.le_ceil _
  have hhiQ : (tauE k ε : ℚ) < (8 * (k : ℚ) / ε) ^ 3 + 1 := Nat.ceil_lt_add_one hq0
  have hlo : (8 * (k : ℝ) / (ε : ℝ)) ^ 3 ≤ (tauE k ε : ℝ) := by exact_mod_cast hloQ
  have hhi' : (tauE k ε : ℝ) < (8 * (k : ℝ) / (ε : ℝ)) ^ 3 + 1 := by exact_mod_cast hhiQ
  have hXk : (k : ℝ) = (ε : ℝ) * (8 * (k : ℝ) / (ε : ℝ)) / 8 := by field_simp
  have h9 : 9 * (k : ℝ) / (ε : ℝ) = 9 * (8 * (k : ℝ) / (ε : ℝ)) / 8 := by ring
  have h8k : 8 * (k : ℝ) ≤ 8 * (k : ℝ) / (ε : ℝ) := by rw [le_div_iff₀ h0R]; nlinarith
  rw [h9]
  generalize 8 * (k : ℝ) / (ε : ℝ) = X at *
  have hX8 : 8 ≤ X := by linarith
  have hX3 : 64 * X ≤ X ^ 3 := by nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ X) (by nlinarith : (0 : ℝ) ≤ X ^ 2 - 64)]
  have hhi : (tauE k ε : ℝ) ≤ (9 * X / 8) ^ 3 := by nlinarith
  refine ⟨?_, ?_, hhi⟩
  · have : ((8 * k : ℕ) : ℝ) ≤ (tauE k ε : ℝ) := by push_cast; linarith
    exact_mod_cast this
  · have := works_of_cube hkR h0R h1R hXk hlo hhi
    simpa [bsumU] using this

end SparsificationLemma.Geo
