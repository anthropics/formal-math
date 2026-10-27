/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsificationLemma.Cal.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Two inequalities between real numbers

This file proves `StSqrt` and `StYLe`.
`StSqrt`: log₂ x + 1 + 16/x ≤ √x for x ≥ 128. With s = √x ≥ 11 the tangent of the logarithm at 16
gives ln s ≤ 4·ln 2 + s/16 − 1, so ln x = 2·ln s ≤ 8·ln 2 + s/8 − 2, and this is at most
(s − 9/8)·ln 2 because ln 2 > 0.693. Finally 16/x ≤ 1/8.
`StYLe`: y ≤ ε for y = 32(k−1)²·log₂(32α)/(32α). With X = 32(k−1)²/ε and t = 32α we have y =
ε·X·log₂ t/t. The function ln t/t decreases for t ≥ e, so it is enough to look at t₀ = 2X·log₂ X,
where t₀ ≤ X² gives
ln t₀/t₀ ≤ 2·ln X/(2X·log₂ X) = ln 2/X. -/

public section

namespace SparsificationLemma.Cal

/-- log₂ x ≤ √x − 9/8 for x ≥ 128. -/
theorem logb_le_sqrt_sub {x : ℝ} (hx : 128 ≤ x) : Real.logb 2 x ≤ Real.sqrt x - 9 / 8 := by
  have hx0 : 0 < x := by linarith
  have hs11 : 11 ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by linarith)
  have hs0 : 0 < Real.sqrt x := by linarith
  have hL1 := Real.log_two_gt_d9
  have hL0 : 0 < Real.log 2 := by linarith
  have h1 : Real.log (Real.sqrt x / 16) ≤ Real.sqrt x / 16 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h2 : Real.log (Real.sqrt x / 16) = Real.log (Real.sqrt x) - 4 * Real.log 2 := by
    rw [Real.log_div hs0.ne' (by norm_num), show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have h3 : Real.log x = 2 * Real.log (Real.sqrt x) := by rw [Real.log_sqrt hx0.le]; ring
  rw [Real.logb, div_le_iff₀ hL0, h3]
  have h5 : 0 ≤ (Real.log 2 - 0.693) * (Real.sqrt x - 73 / 8) := mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- log₂ x + 1 + 16/x ≤ √x for x ≥ 128. -/
theorem stSqrt : StSqrt := by
  intro x hx
  have hx0 : 0 < x := by linarith
  have h16 : 16 / x ≤ 1 / 8 := by rw [div_le_iff₀ hx0]; linarith
  have h4 := logb_le_sqrt_sub hx
  linarith

/-- 7 ≤ log₂ x for x ≥ 128. -/
theorem seven_le_logb {x : ℝ} (hx : 128 ≤ x) : 7 ≤ Real.logb 2 x := by
  have h : Real.logb 2 128 = 7 := by
    rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
    norm_num
  rw [← h]
  exact Real.logb_le_logb_of_le (by norm_num) (by norm_num) hx

/-- 2·log₂ x ≤ x for x ≥ 128. -/
theorem two_logb_le {x : ℝ} (hx : 128 ≤ x) : 2 * Real.logb 2 x ≤ x := by
  have hx0 : 0 ≤ x := by linarith
  have hs11 : 11 ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by linarith)
  have hs2 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0
  have h4 := logb_le_sqrt_sub hx
  nlinarith

/-- ε·X·log₂ t/t ≤ ε for X ≥ 128 and t ≥ 2X·log₂ X. -/
theorem mul_logb_div_le {X t ε : ℝ} (hε : 0 < ε) (hX : 128 ≤ X) (ht : 2 * X * Real.logb 2 X ≤ t) :
    ε * X * Real.logb 2 t / t ≤ ε := by
  have hX0 : 0 < X := by linarith
  have hL0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h7 := seven_le_logb hX
  have hl0 : 0 < Real.logb 2 X := by linarith
  have hlX : Real.log X = Real.logb 2 X * Real.log 2 := by rw [Real.logb, div_mul_cancel₀ _ hL0.ne']
  have ht0 : 0 < 2 * X * Real.logb 2 X := by positivity
  have htpos : 0 < t := by linarith
  have he : Real.exp 1 ≤ 2 * X * Real.logb 2 X := by
    have := Real.exp_one_lt_d9
    nlinarith
  have hanti : Real.log t / t ≤ Real.log (2 * X * Real.logb 2 X) / (2 * X * Real.logb 2 X) :=
    Real.log_div_self_antitoneOn he (le_trans he ht) ht
  have hsq : Real.log (2 * X * Real.logb 2 X) ≤ 2 * Real.log X := by
    have h2 := two_logb_le hX
    have : Real.log (2 * X * Real.logb 2 X) ≤ Real.log (X ^ 2) := Real.log_le_log ht0 (by nlinarith)
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  have h1 : Real.log t / t ≤ Real.log 2 / X := by
    refine hanti.trans ?_
    rw [div_le_div_iff₀ ht0 hX0]
    rw [hlX] at hsq
    nlinarith
  have h2 : X * Real.log t ≤ t * Real.log 2 := by
    rw [div_le_div_iff₀ htpos hX0] at h1
    linarith
  have h3 : X * Real.logb 2 t ≤ t := by
    rw [Real.logb, ← mul_div_assoc, div_le_iff₀ hL0]
    exact h2
  rw [div_le_iff₀ htpos]
  nlinarith

/-- y ≤ ε whenever 32α ≥ 2x·log₂ x and x = 32(k−1)²/ε ≥ 128. -/
theorem stYLe : StYLe := by
  intro k α ε _ hε hX ht
  have hA : 32 * ((k : ℝ) - 1) ^ 2 = ε * (32 * ((k : ℝ) - 1) ^ 2 / ε) := by field_simp
  have h := mul_logb_div_le hε hX ht
  rw [← hA] at h
  exact h

end SparsificationLemma.Cal
