/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClausesOccurStatement
import OccurM.Arith
import VariableBound.Paper.Arith
import Wrap.Arith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! # The polynomial in the length of the formula is absorbed when every variable occurs

If all n variables occur then n ≤ k·m, and the code with n in unary has at most 8·(k·m)² bits.
Throughout 0 ≤ α ≤ 1, k ≥ 1 and m ≥ 2, and Y = k·m/(log₂(m+2))^α is the exponent of the bound
`SatM.bound`.

1. `sq_lg_add_two_le`: (log₂(m+2))² ≤ 128·m.
2. `lg_mul_le`: log(k·m) ≤ 130·Y.
3. `back_le`: 2^{C·km/(log m)^α} + C·a^C ≤ C'·2^{C'·Y} with C' = 650·C + 1, for every a ≤ 8·(k·m)².

Only numbers; no machine and no formula occurs in this file. -/

public section

namespace OccurM

open MainTheoremForms ClausesOccur VariableBound.Paper

variable {α : ℝ} {k m : ℕ}

/-- (log₂(m+2))² ≤ 128·m for m ≥ 2. -/
theorem sq_lg_add_two_le (hm : 2 ≤ m) : lg ((m : ℝ) + 2) * lg ((m : ℝ) + 2) ≤ 128 * m := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hy : (0 : ℝ) < (m : ℝ) + 2 := by linarith
  have h8 := Wrap.Arith.lg_le_fourth_root hy
  have hl0 : 0 ≤ lg ((m : ℝ) + 2) := by linarith [lg_mono two_pos (by linarith : (2 : ℝ) ≤ (m : ℝ) + 2), lg_two]
  have hs0 : 0 ≤ Real.sqrt (Real.sqrt ((m : ℝ) + 2)) := Real.sqrt_nonneg _
  have hss : Real.sqrt (Real.sqrt ((m : ℝ) + 2)) * Real.sqrt (Real.sqrt ((m : ℝ) + 2)) = Real.sqrt ((m : ℝ) + 2) := Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have hle : Real.sqrt ((m : ℝ) + 2) ≤ (m : ℝ) + 2 := Real.sqrt_le_iff.2 ⟨hy.le, by nlinarith⟩
  have hmul := mul_le_mul h8 h8 hl0 (by positivity)
  nlinarith

/-- log(k·m) ≤ 130·k·m/(log₂(m+2))^α. -/
theorem lg_mul_le (h1 : α ≤ 1) (hk : 1 ≤ k) (hm : 2 ≤ m) : lg ((k : ℝ) * m) ≤ 130 * ((k : ℝ) * m * SatM.rPow α m) := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hL1 : 1 ≤ lg ((m : ℝ) + 2) := by linarith [lg_mono two_pos (by linarith : (2 : ℝ) ≤ (m : ℝ) + 2), lg_two]
  have hLm : lg m ≤ lg ((m : ℝ) + 2) := lg_mono (by linarith) (by linarith)
  have hp : 0 < lg ((m : ℝ) + 2) ^ α := Real.rpow_pos_of_pos (by linarith) α
  have hpl : lg ((m : ℝ) + 2) ^ α ≤ lg ((m : ℝ) + 2) := by
    have h := Real.rpow_le_rpow_of_exponent_le hL1 h1
    rwa [Real.rpow_one] at h
  have hsplit : lg ((k : ℝ) * m) = lg k + lg m := by
    unfold lg
    exact Real.logb_mul (by linarith) (by linarith)
  have hlk : lg k ≤ k := by linarith [lg_le_sub_one hk]
  have hlk0 : 0 ≤ lg k := by
    have h := lg_mono one_pos hk1
    unfold lg at h ⊢
    rwa [Real.logb_one] at h
  have hlm0 : 0 ≤ lg m := by linarith [one_le_lg hm]
  have hL2m : lg ((m : ℝ) + 2) ≤ 2 * m := by linarith [lg_add_two_le hm, lg_le_sub_one (by omega : 1 ≤ m)]
  have ha : lg k * lg ((m : ℝ) + 2) ≤ k * (2 * m) := mul_le_mul hlk hL2m (by linarith) (by linarith)
  have hb : lg m * lg ((m : ℝ) + 2) ≤ 128 * m := (mul_le_mul_of_nonneg_right hLm (by linarith)).trans (sq_lg_add_two_le hm)
  have hkm : (m : ℝ) ≤ k * m := by nlinarith
  have hmain : lg ((k : ℝ) * m) * lg ((m : ℝ) + 2) ^ α ≤ 130 * ((k : ℝ) * m) := by
    calc lg ((k : ℝ) * m) * lg ((m : ℝ) + 2) ^ α ≤ lg ((k : ℝ) * m) * lg ((m : ℝ) + 2) := mul_le_mul_of_nonneg_left hpl (by rw [hsplit]; linarith)
      _ = lg k * lg ((m : ℝ) + 2) + lg m * lg ((m : ℝ) + 2) := by rw [hsplit]; ring
      _ ≤ 130 * ((k : ℝ) * m) := by linarith
  have e : 130 * ((k : ℝ) * m * SatM.rPow α m) = 130 * ((k : ℝ) * m) / lg ((m : ℝ) + 2) ^ α := by
    unfold SatM.rPow lg
    ring
  rw [e, le_div_iff₀ hp]
  exact hmain

/-- The printed bound with the constant C, plus C·a^C for a number a ≤ 8·(k·m)², is at most the
bound `SatM.bound`, with exponent k·m/(log₂(m+2))^α, for the constant 650·C + 1. -/
theorem back_le (h0 : 0 ≤ α) (h1 : α ≤ 1) (C : ℕ) (hk : 1 ≤ k) (hm : 2 ≤ m) {a : ℕ} (ha : a ≤ 8 * (k * m) ^ 2) :
    timeClauses α C k m + C * a ^ C ≤ SatM.bound (SatM.rPow α) (650 * C + 1) k m := by
  have hX := one_le_expClauses h0 h1 hk hm
  have hXY := expClauses_le h0 h1 k hm
  have hlg := lg_mul_le h1 hk hm
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  set Y : ℝ := (k : ℝ) * m * SatM.rPow α m with hY
  have hY0 : 0 ≤ Y := by linarith
  have hs2 : 2 ≤ k * m := by nlinarith
  have hs0 : (0 : ℝ) < (k : ℝ) * m := by exact_mod_cast (by omega : 0 < k * m)
  have ha5 : a ≤ (k * m) ^ 5 := by
    calc a ≤ 2 ^ 3 * (k * m) ^ 2 := ha
      _ ≤ (k * m) ^ 3 * (k * m) ^ 2 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hs2 3)
      _ = (k * m) ^ 5 := by ring
  have hbig : ∀ t : ℝ, t ≤ (650 * C + 1) * Y → (2 : ℝ) ^ t ≤ (2 : ℝ) ^ ((650 * (C : ℝ) + 1) * Y) := fun t ht => Real.rpow_le_rpow_of_exponent_le one_le_two ht
  have ht : ((timeClauses α C k m : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((650 * (C : ℝ) + 1) * Y) := by
    unfold timeClauses
    refine (Nat.floor_le (by positivity)).trans (hbig _ ?_)
    nlinarith [mul_le_mul_of_nonneg_left hXY hC0, mul_nonneg hC0 hY0]
  have hpw : ((a : ℝ)) ^ C ≤ (2 : ℝ) ^ ((650 * (C : ℝ) + 1) * Y) := by
    have h5 : (a : ℝ) ≤ ((k : ℝ) * m) ^ 5 := by exact_mod_cast ha5
    have e2 : ((k : ℝ) * m) = (2 : ℝ) ^ lg ((k : ℝ) * m) := by
      unfold lg
      rw [Real.rpow_logb two_pos (by norm_num) hs0]
    calc (a : ℝ) ^ C ≤ (((k : ℝ) * m) ^ 5) ^ C := pow_le_pow_left₀ (Nat.cast_nonneg a) h5 C
      _ = ((k : ℝ) * m) ^ (5 * C) := (pow_mul _ _ _).symm
      _ = ((2 : ℝ) ^ lg ((k : ℝ) * m)) ^ (5 * C) := by rw [← e2]
      _ = (2 : ℝ) ^ (lg ((k : ℝ) * m) * ((5 * C : ℕ) : ℝ)) := (Real.rpow_mul_natCast two_pos.le _ _).symm
      _ ≤ _ := hbig _ (by
        push_cast
        nlinarith [mul_le_mul_of_nonneg_right hlg hC0, mul_nonneg hC0 hY0])
  have hp0 : (0 : ℝ) < (2 : ℝ) ^ ((650 * (C : ℝ) + 1) * Y) := by positivity
  unfold SatM.bound
  refine Nat.le_floor ?_
  have e : (((650 * C + 1 : ℕ) : ℝ)) * k * m * SatM.rPow α m = (650 * (C : ℝ) + 1) * Y := by
    rw [hY]
    push_cast
    ring
  rw [e]
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hpw hC0, mul_nonneg hC0 hp0.le]

end OccurM
