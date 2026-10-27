/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClausesOccurStatement
import VariableBound.Paper.Arith
import VariableBound.Paper.Rename.Time
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! # From the bound C·2^{C·km/(log₂(m+2))^α} of `SatM.bound` to the printed bound 2^{C·km/(log m)^α} + C·(length)^C

The bound `SatM.bound (SatM.rPow α) C` is C·2^{C·k·m/(log₂(m+2))^α}, the printed one 2^{C·km/(log
m)^α} plus a polynomial in the length of the formula. Throughout 0 ≤ α ≤ 1, k ≥ 1 and m ≥ 2, and X
is the printed exponent km/(log m)^α.

1. `ClausesOccur.expHalf`: at α = ½ the printed exponent is that of the Main Theorem.
2. `one_le_expClauses`: X ≥ 1. `shift_le`, `expClauses_le`: k·m/(log₂(m+2))^α ≤ X ≤
   2·k·m/(log₂(m+2))^α.
3. `pow_le_timeClauses`, `timeClauses_mono`: powers of two below the printed bound; the printed
   bound grows with the constant.
4. `bound_le_pow`: the bound `SatM.bound` with the constant C is at most 2^E for a natural number E
   ≤ (2C+1)·X.
5. `steps_le`: q·(a + 2^E + 1)^q, with E ≤ G·X, X ≥ 1 and a ≥ 1, is at most the printed bound plus
   the polynomial in a, both with the constant `stepsC q G`.

Only numbers; no machine and no formula occurs in this file. -/

public section

namespace ClausesOccur

open MainTheoremForms

/-- At α = ½ the exponent is that of the Main Theorem. -/
theorem expHalf : ExpHalfStmt := by
  intro k m
  unfold expClauses expM
  rw [Real.sqrt_eq_rpow]

end ClausesOccur

namespace OccurM

open MainTheoremForms ClausesOccur VariableBound.Paper

variable {α : ℝ} {k m : ℕ}

/-! ### The printed exponent -/

/-- (log m)^α ≥ 1. -/
theorem one_le_lg_rpow (h0 : 0 ≤ α) (hm : 2 ≤ m) : 1 ≤ lg m ^ α := Real.one_le_rpow (one_le_lg hm) h0

/-- (log m)^α ≤ log m. -/
theorem lg_rpow_le (h1 : α ≤ 1) (hm : 2 ≤ m) : lg m ^ α ≤ lg m := by
  have h := Real.rpow_le_rpow_of_exponent_le (one_le_lg hm) h1
  rwa [Real.rpow_one] at h

/-- The printed exponent is at least 1. -/
theorem one_le_expClauses (h0 : 0 ≤ α) (h1 : α ≤ 1) (hk : 1 ≤ k) (hm : 2 ≤ m) : 1 ≤ expClauses α k m := by
  have hp := one_le_lg_rpow h0 hm
  have hle : lg m ^ α ≤ m := (lg_rpow_le h1 hm).trans (by linarith [lg_le_sub_one (by omega : 1 ≤ m)])
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  unfold expClauses
  rw [le_div_iff₀ (by linarith)]
  nlinarith [mul_nonneg (sub_nonneg.2 hk') hm0]

/-- k·m/(log₂(m+2))^α ≤ k·m/(log m)^α. -/
theorem shift_le (h0 : 0 ≤ α) (k : ℕ) (hm : 2 ≤ m) : (k : ℝ) * m * SatM.rPow α m ≤ expClauses α k m := by
  have h1 := one_le_lg hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hp : 0 < lg m ^ α := Real.rpow_pos_of_pos (by linarith) α
  have hle : lg m ^ α ≤ lg ((m : ℝ) + 2) ^ α := Real.rpow_le_rpow (by linarith) (lg_mono hm0 (by linarith)) h0
  unfold SatM.rPow expClauses
  rw [mul_one_div]
  exact div_le_div_of_nonneg_left (by positivity) hp hle

/-- log₂(m+2) ≤ 2·log m, since m + 2 ≤ m². -/
theorem lg_add_two_le (hm : 2 ≤ m) : lg ((m : ℝ) + 2) ≤ 2 * lg m := by
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have h : lg ((m : ℝ) ^ 2) = 2 * lg m := by
    unfold lg
    rw [Real.logb_pow]
    norm_num
  rw [← h]
  exact lg_mono (by linarith) (by nlinarith)

/-- (log₂(m+2))^α ≤ 2·(log m)^α. -/
theorem lg_add_two_rpow_le (h0 : 0 ≤ α) (h1 : α ≤ 1) (hm : 2 ≤ m) : lg ((m : ℝ) + 2) ^ α ≤ 2 * lg m ^ α := by
  have hl := one_le_lg hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hl2 : 0 ≤ lg ((m : ℝ) + 2) := by linarith [lg_mono hm0 (by linarith : (m : ℝ) ≤ (m : ℝ) + 2)]
  have h2 : (2 : ℝ) ^ α ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le one_le_two h1
    rwa [Real.rpow_one] at h
  calc lg ((m : ℝ) + 2) ^ α ≤ (2 * lg m) ^ α := Real.rpow_le_rpow hl2 (lg_add_two_le hm) h0
    _ = 2 ^ α * lg m ^ α := Real.mul_rpow (by norm_num) (by linarith)
    _ ≤ 2 * lg m ^ α := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (by linarith) α)

/-- k·m/(log m)^α ≤ 2·k·m/(log₂(m+2))^α. -/
theorem expClauses_le (h0 : 0 ≤ α) (h1 : α ≤ 1) (k : ℕ) (hm : 2 ≤ m) : expClauses α k m ≤ 2 * ((k : ℝ) * m * SatM.rPow α m) := by
  have hl := one_le_lg hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hl2 : 0 < lg ((m : ℝ) + 2) := by linarith [lg_mono hm0 (by linarith : (m : ℝ) ≤ (m : ℝ) + 2)]
  have hp : 0 < lg m ^ α := Real.rpow_pos_of_pos (by linarith) α
  have hp2 : 0 < lg ((m : ℝ) + 2) ^ α := Real.rpow_pos_of_pos hl2 α
  have hr : 1 / lg m ^ α ≤ 2 * (1 / lg ((m : ℝ) + 2) ^ α) := by
    rw [div_le_iff₀ hp]
    have e : 2 * (1 / lg ((m : ℝ) + 2) ^ α) * lg m ^ α = 2 * lg m ^ α / lg ((m : ℝ) + 2) ^ α := by ring
    rw [e, le_div_iff₀ hp2, one_mul]
    exact lg_add_two_rpow_le h0 h1 hm
  have hkm : (0 : ℝ) ≤ (k : ℝ) * m := by positivity
  calc expClauses α k m = (k : ℝ) * m * (1 / lg m ^ α) := by unfold expClauses; ring
    _ ≤ (k : ℝ) * m * (2 * (1 / lg ((m : ℝ) + 2) ^ α)) := mul_le_mul_of_nonneg_left hr hkm
    _ = 2 * ((k : ℝ) * m * SatM.rPow α m) := by unfold SatM.rPow lg; ring

/-! ### The printed bound -/

/-- 2^e is at most the printed bound with the constant C if e ≤ C·X. -/
theorem pow_le_timeClauses {e C : ℕ} (h : (e : ℝ) ≤ C * expClauses α k m) : 2 ^ e ≤ timeClauses α C k m := by
  unfold timeClauses
  refine Nat.le_floor ?_
  push_cast
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le one_le_two h

/-- The printed bound grows with the constant. -/
theorem timeClauses_mono {C C' : ℕ} (h : C ≤ C') (hX : 0 ≤ expClauses α k m) : timeClauses α C k m ≤ timeClauses α C' k m := by
  unfold timeClauses
  exact Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_right (by exact_mod_cast h) hX))

/-- The bound `SatM.bound` with the constant C is at most 2^E for a natural number E ≤ (2C+1)·X: the
factor in front goes into the exponent. -/
theorem bound_le_pow (h0 : 0 ≤ α) (h1 : α ≤ 1) (C : ℕ) (hk : 1 ≤ k) (hm : 2 ≤ m) :
    ∃ E : ℕ, SatM.bound (SatM.rPow α) C k m ≤ 2 ^ E ∧ (E : ℝ) ≤ ((2 * C + 1 : ℕ) : ℝ) * expClauses α k m := by
  have hX := one_le_expClauses h0 h1 hk hm
  have hs := shift_le h0 k hm
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  have hpos : 0 ≤ (C : ℝ) + C * expClauses α k m := add_nonneg hC0 (mul_nonneg hC0 (by linarith))
  refine ⟨⌈(C : ℝ) + C * expClauses α k m⌉₊, ?_, ?_⟩
  · have hC2 : (C : ℝ) ≤ (2 : ℝ) ^ (C : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast Nat.lt_two_pow_self.le
    have e : (C : ℝ) * k * m * SatM.rPow α m = (C : ℝ) * ((k : ℝ) * m * SatM.rPow α m) := by ring
    have hb : ((SatM.bound (SatM.rPow α) C k m : ℕ) : ℝ) ≤ (2 : ℝ) ^ ((C : ℝ) + C * expClauses α k m) := by
      unfold SatM.bound
      calc _ ≤ (C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * k * m * SatM.rPow α m) := Nat.floor_le (by positivity)
        _ ≤ (2 : ℝ) ^ (C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * expClauses α k m) := by
          rw [e]
          exact mul_le_mul hC2 (Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_left hs hC0)) (by positivity) (by positivity)
        _ = _ := (Real.rpow_add two_pos _ _).symm
    have h2 := Real.rpow_le_rpow_of_exponent_le one_le_two (Nat.le_ceil ((C : ℝ) + C * expClauses α k m))
    rw [Real.rpow_natCast] at h2
    exact_mod_cast hb.trans h2
  · have h := (Nat.ceil_lt_add_one hpos).le
    push_cast
    nlinarith [mul_nonneg hC0 (sub_nonneg.2 hX)]

/-! ### The steps of a machine that runs on a pad of 2^E units, or around a machine with 2^E steps -/

/-- The constant of `steps_le`. -/
def stepsC (q G : ℕ) : ℕ := max (4 * q + 2 * q * G) (q * 4 ^ q)

/-- q·(a + 2^E + 1)^q, with E ≤ G·X, X ≥ 1 and a ≥ 1, is at most 2^{C·X} + C·a^C with C =
`stepsC q G`. -/
theorem steps_le (q G : ℕ) {E a : ℕ} (hE : (E : ℝ) ≤ G * expClauses α k m) (hX : 1 ≤ expClauses α k m) (ha : 1 ≤ a) :
    q * (a + 2 ^ E + 1) ^ q ≤ timeClauses α (stepsC q G) k m + stepsC q G * a ^ stepsC q G := by
  refine (VariableBound.Rename.steps_split q a 0 E).trans ?_
  rw [add_comm]
  refine Nat.add_le_add ?_ ((VariableBound.Rename.poly_le q ha).trans (VariableBound.Rename.poly_mono (le_max_right _ _) ha))
  have hb : 0 + 2 ^ E + 1 ≤ 2 ^ (E + 1) := by
    have := Nat.one_le_two_pow (n := E)
    rw [pow_succ]
    omega
  have h1 : 2 * q * (0 + 2 ^ E + 1) ^ (2 * q) ≤ 2 ^ (2 * q + (E + 1) * (2 * q)) := by
    calc 2 * q * (0 + 2 ^ E + 1) ^ (2 * q) ≤ 2 ^ (2 * q) * (2 ^ (E + 1)) ^ (2 * q) :=
          Nat.mul_le_mul Nat.lt_two_pow_self.le (Nat.pow_le_pow_left hb _)
      _ = 2 ^ (2 * q + (E + 1) * (2 * q)) := by rw [← pow_mul, ← pow_add]
  refine h1.trans ((pow_le_timeClauses (C := 4 * q + 2 * q * G) ?_).trans (timeClauses_mono (le_max_left _ _) (by linarith)))
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  push_cast
  nlinarith [mul_nonneg hq (sub_nonneg.2 hX), mul_nonneg hq (sub_nonneg.2 hE)]

end OccurM
