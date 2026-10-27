/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import MainTheoremFormsStatement
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-! # From log₂(m+2), log₂(n+4) and a factor in front to the printed bounds

`UniformInKStatement.lean` has the bounds C·2^{C·k²·n·log₂ log₂(n+4)/√(log₂(n+4))} and
C·2^{C·min(that exponent, k·m/√(log₂(m+2)))}. `MainTheoremFormsStatement.lean` has 2^{C·k²·n·log log
n/√(log n)} for n ≥ 4 and
2^{C·min{km/√(log m), k²·n·log log n/√(log n)}} for m ≥ 2 and n ≥ 4. Here:

1. `two_le_expM`, `two_le_base`: km/√(log m) (k ≥ 1, m ≥ 2) and n·log log n/√(log n) (n ≥ 4) are at
   least 2 (proof of Corollary 11).
2. `boundNK_le`, `boundBothK_le`: the bounds with the constant C are at most the printed bounds with
   the constant 3C.
3. `timeCor_eq`: the minimum of the two powers is the power of the minimum («This is the Main
   Theorem»).
4. `timeMin_three_le`: at k = 3 the printed bound with C is at most the bound without k with 9C.

Only real numbers; no machine and no formula occurs in this file. -/

public section

namespace VariableBound.Paper

open MainTheoremForms

/-! ### The logarithm -/

/-- log x ≤ log y for 0 < x ≤ y. -/
theorem lg_mono {x y : ℝ} (hx : 0 < x) (h : x ≤ y) : lg x ≤ lg y := Real.logb_le_logb_of_le one_lt_two hx h

/-- log 2 = 1. -/
theorem lg_two : lg 2 = 1 := Real.logb_self_eq_one one_lt_two

/-- log(2x) = 1 + log x for x > 0. -/
theorem lg_two_mul {x : ℝ} (hx : 0 < x) : lg (2 * x) = 1 + lg x := by
  unfold lg
  rw [Real.logb_mul (by norm_num) hx.ne', Real.logb_self_eq_one one_lt_two]

/-- log m ≥ 1 for m ≥ 2. -/
theorem one_le_lg {m : ℕ} (hm : 2 ≤ m) : 1 ≤ lg m := by
  rw [← lg_two]
  exact lg_mono two_pos (by exact_mod_cast hm)

/-- log m ≤ m − 1 for m ≥ 1. -/
theorem lg_le_sub_one {m : ℕ} (hm : 1 ≤ m) : lg m ≤ (m : ℝ) - 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have h : ((j + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ j := by exact_mod_cast (Nat.lt_two_pow_self (n := j))
  unfold lg
  rw [Real.logb_le_iff_le_rpow one_lt_two (by positivity)]
  have e : ((j + 1 : ℕ) : ℝ) - 1 = (j : ℝ) := by push_cast; ring
  rw [e, Real.rpow_natCast]
  exact h

/-- 2·√(log m) ≤ m for m ≥ 1. -/
theorem two_sqrt_lg_le {m : ℕ} (hm : 1 ≤ m) : 2 * Real.sqrt (lg m) ≤ m := by
  have h1 := lg_le_sub_one hm
  have h2 : Real.sqrt (lg m) ≤ (m : ℝ) / 2 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    nlinarith [sq_nonneg ((m : ℝ) - 2)]
  linarith

/-- For n ≥ 4: 2 ≤ log n ≤ log(n+4), 1 ≤ log log n, and 0 ≤ log log(n+4) ≤ 2·log log n. -/
theorem lg_add_four {n : ℕ} (hn : 4 ≤ n) :
    2 ≤ lg n ∧ lg n ≤ lg ((n : ℝ) + 4) ∧ 1 ≤ lg (lg n) ∧ 0 ≤ lg (lg ((n : ℝ) + 4)) ∧ lg (lg ((n : ℝ) + 4)) ≤ 2 * lg (lg n) := by
  have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hL2 : 2 ≤ lg n := by
    have h4 : lg 4 = 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, lg_two_mul two_pos, lg_two]
      norm_num
    rw [← h4]
    exact lg_mono (by norm_num) hn4
  have hLL' : lg n ≤ lg ((n : ℝ) + 4) := lg_mono (by linarith) (by linarith)
  have hL'2 : lg ((n : ℝ) + 4) ≤ 2 * lg n := by
    have h2 : lg ((n : ℝ) + 4) ≤ lg (2 * n) := lg_mono (by linarith) (by linarith)
    have h3 := lg_two_mul (x := (n : ℝ)) (by linarith)
    linarith
  have hl1 : 1 ≤ lg (lg n) := by
    rw [← lg_two]
    exact lg_mono two_pos hL2
  have hl' : lg (lg ((n : ℝ) + 4)) ≤ 2 * lg (lg n) := by
    have h1 : lg (lg ((n : ℝ) + 4)) ≤ lg (2 * lg n) := lg_mono (by linarith) hL'2
    have h2 := lg_two_mul (x := lg n) (by linarith)
    linarith
  have hl0 : 0 ≤ lg (lg ((n : ℝ) + 4)) := by
    have : lg (lg n) ≤ lg (lg ((n : ℝ) + 4)) := lg_mono (by linarith) hLL'
    linarith
  exact ⟨hL2, hLL', hl1, hl0, hl'⟩

/-! ### Both exponents are at least 2 -/

/-- k·m/√(log m) ≥ 2 for k ≥ 1 and m ≥ 2. -/
theorem two_le_expM {k m : ℕ} (hk : 1 ≤ k) (hm : 2 ≤ m) : 2 ≤ expM k m := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hs : 0 < Real.sqrt (lg m) := Real.sqrt_pos.2 (by linarith [one_le_lg hm])
  have h2 := two_sqrt_lg_le (m := m) (by omega)
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  unfold expM
  rw [le_div_iff₀ hs]
  nlinarith

/-- n·log log n/√(log n) ≥ 2 for n ≥ 4. -/
theorem two_le_base {n : ℕ} (hn : 4 ≤ n) : 2 ≤ (n : ℝ) * lg (lg n) / Real.sqrt (lg n) := by
  obtain ⟨hL2, -, hl1, -, -⟩ := lg_add_four hn
  have hs : 0 < Real.sqrt (lg n) := Real.sqrt_pos.2 (by linarith)
  have h2 := two_sqrt_lg_le (m := n) (by omega)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [le_div_iff₀ hs]
  nlinarith

/-- The exponent in n is k² times n·log log n/√(log n). -/
theorem expN_eq (k n : ℕ) : expN k n = (k : ℝ) ^ 2 * ((n : ℝ) * lg (lg n) / Real.sqrt (lg n)) := by
  unfold expN
  ring

/-- The exponent in m is k times m/√(log m). -/
theorem expM_eq (k m : ℕ) : expM k m = (k : ℝ) * ((m : ℝ) / Real.sqrt (lg m)) := by
  unfold expM
  ring

/-- k²·n·log log n/√(log n) ≥ 2 for k ≥ 1 and n ≥ 4. -/
theorem two_le_expN {k n : ℕ} (hk : 1 ≤ k) (hn : 4 ≤ n) : 2 ≤ expN k n := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h := two_le_base hn
  have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ hk1
  rw [expN_eq]
  nlinarith

/-! ### The exponents with shifts against the printed exponents -/

/-- k·m/√(log₂(m+2)) ≤ k·m/√(log m) for m ≥ 2. -/
theorem shiftM_le (k : ℕ) {m : ℕ} (hm : 2 ≤ m) : (k : ℝ) * m * SatM.rPow (1 / 2) m ≤ expM k m := by
  have h1 := one_le_lg hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hs : 0 < Real.sqrt (lg m) := Real.sqrt_pos.2 (by linarith)
  have hle : Real.sqrt (lg m) ≤ Real.sqrt (lg ((m : ℝ) + 2)) := Real.sqrt_le_sqrt (lg_mono hm0 (by linarith))
  unfold SatM.rPow expM
  rw [← Real.sqrt_eq_rpow, mul_one_div]
  exact div_le_div_of_nonneg_left (by positivity) hs hle

/-- k²·n·log₂ log₂(n+4)/√(log₂(n+4)) ≤ 2·k²·n·log log n/√(log n) for n ≥ 4. -/
theorem shiftN_le (k : ℕ) {n : ℕ} (hn : 4 ≤ n) : (k : ℝ) ^ 2 * n * SatK.rN 1 (1 / 2) n ≤ 2 * expN k n := by
  obtain ⟨hL2, hLL', hl1, hl0, hl'⟩ := lg_add_four hn
  have hs : 0 < Real.sqrt (lg n) := Real.sqrt_pos.2 (by linarith)
  have hle : Real.sqrt (lg n) ≤ Real.sqrt (lg ((n : ℝ) + 4)) := Real.sqrt_le_sqrt hLL'
  have hr : SatK.rN 1 (1 / 2) n ≤ 2 * (lg (lg n) / Real.sqrt (lg n)) := by
    unfold SatK.rN
    rw [← Real.sqrt_eq_rpow, pow_one]
    change lg (lg ((n : ℝ) + 4)) / Real.sqrt (lg ((n : ℝ) + 4)) ≤ _
    calc lg (lg ((n : ℝ) + 4)) / Real.sqrt (lg ((n : ℝ) + 4)) ≤ lg (lg ((n : ℝ) + 4)) / Real.sqrt (lg n) :=
          div_le_div_of_nonneg_left hl0 hs hle
      _ ≤ 2 * lg (lg n) / Real.sqrt (lg n) := div_le_div_of_nonneg_right hl' hs.le
      _ = 2 * (lg (lg n) / Real.sqrt (lg n)) := mul_div_assoc _ _ _
  calc (k : ℝ) ^ 2 * n * SatK.rN 1 (1 / 2) n ≤ (k : ℝ) ^ 2 * n * (2 * (lg (lg n) / Real.sqrt (lg n))) :=
        mul_le_mul_of_nonneg_left hr (by positivity)
    _ = 2 * expN k n := by unfold expN; ring

/-! ### The factor in front goes into the exponent -/

/-- C ≤ 2^{C·X} for X ≥ 1. -/
theorem natCast_le_two_rpow (C : ℕ) {X : ℝ} (hX : 1 ≤ X) : (C : ℝ) ≤ (2 : ℝ) ^ ((C : ℝ) * X) := by
  have h1 : (C : ℝ) ≤ (2 : ℝ) ^ (C : ℝ) := by
    rw [Real.rpow_natCast]
    exact_mod_cast Nat.lt_two_pow_self.le
  exact h1.trans (Real.rpow_le_rpow_of_exponent_le one_le_two (le_mul_of_one_le_right (Nat.cast_nonneg C) hX))

/-- If E ≤ 2·X and X ≥ 1, then C·2^{C·E} ≤ 2^{3C·X}. -/
theorem absorb (C : ℕ) {E X : ℝ} (hE : E ≤ 2 * X) (hX : 1 ≤ X) : (C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * E) ≤ (2 : ℝ) ^ (((3 * C : ℕ) : ℝ) * X) := by
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  calc (C : ℝ) * (2 : ℝ) ^ ((C : ℝ) * E) ≤ (2 : ℝ) ^ ((C : ℝ) * X) * (2 : ℝ) ^ ((C : ℝ) * (2 * X)) :=
        mul_le_mul (natCast_le_two_rpow C hX) (Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_left hE hC0)) (by positivity) (by positivity)
    _ = (2 : ℝ) ^ (((3 * C : ℕ) : ℝ) * X) := by
      rw [← Real.rpow_add two_pos]
      congr 1
      push_cast
      ring

/-- For k ≥ 1 and n ≥ 4 the bound in n of `UniformInKStatement.lean` with the constant C is at most
the printed bound of Theorem D (b) with the constant 3C. -/
theorem boundNK_le (C : ℕ) {k n : ℕ} (hk : 1 ≤ k) (hn : 4 ≤ n) : SatM.boundNK (SatK.rN 1 (1 / 2)) C k n ≤ timeN (3 * C) k n := by
  unfold SatM.boundNK timeN
  refine Nat.floor_le_floor ?_
  have e : (C : ℝ) * (k : ℝ) ^ 2 * n * SatK.rN 1 (1 / 2) n = (C : ℝ) * ((k : ℝ) ^ 2 * n * SatK.rN 1 (1 / 2) n) := by ring
  rw [e]
  exact absorb C (shiftN_le k hn) (by linarith [two_le_expN hk hn])

/-- For k ≥ 1, m ≥ 2 and n ≥ 4 the bound with the minimum of `UniformInKStatement.lean` with the
constant C is at most the printed bound of Theorem 1 with the constant 3C. -/
theorem boundBothK_le (C : ℕ) {k m n : ℕ} (hk : 1 ≤ k) (hm : 2 ≤ m) (hn : 4 ≤ n) :
    SatM.boundBothK (SatK.rN 1 (1 / 2)) (SatM.rPow (1 / 2)) C k n m ≤ timeMin (3 * C) k m n := by
  unfold SatM.boundBothK timeMin
  refine Nat.floor_le_floor (absorb C ?_ ?_)
  · have hM := shiftM_le k hm
    have hN := shiftN_le k hn
    have hM2 := two_le_expM hk hm
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    exact le_min ((min_le_right _ _).trans (by linarith)) ((min_le_left _ _).trans hN)
  · exact le_min (by linarith [two_le_expM hk hm]) (by linarith [two_le_expN hk hn])

/-! ### The printed bounds among themselves -/

/-- The printed bound of Theorem 1 grows with the constant, for k ≥ 1, m ≥ 2 and n ≥ 4. -/
theorem timeMin_mono {C C' : ℕ} (h : C ≤ C') {k m n : ℕ} (hk : 1 ≤ k) (hm : 2 ≤ m) (hn : 4 ≤ n) : timeMin C k m n ≤ timeMin C' k m n := by
  unfold timeMin
  have hX : 0 ≤ min (expM k m) (expN k n) := le_min (by linarith [two_le_expM hk hm]) (by linarith [two_le_expN hk hn])
  exact Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_right (by exact_mod_cast h) hX))

/-- min{2^{C·a}, 2^{C·b}} = 2^{C·min{a, b}}: the time of Corollary 11 is the time of Theorem 1. No
hypothesis on C, k, m, n. -/
theorem timeCor_eq (C k m n : ℕ) : timeCor C k m n = timeMin C k m n := by
  have hmono : Monotone fun x : ℝ => (2 : ℝ) ^ ((C : ℝ) * x) := fun x y hxy =>
    Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_left hxy (Nat.cast_nonneg C))
  unfold timeCor timeMin
  rw [hmono.map_min]

/-- At k = 3 the printed bound of Theorem 1 with the constant C is at most 2^{9C·min{m/√(log m),
n·log log n/√(log n)}}, for m ≥ 2 and n ≥ 4. -/
theorem timeMin_three_le (C : ℕ) {m n : ℕ} (hm : 2 ≤ m) (hn : 4 ≤ n) : timeMin C 3 m n ≤ timeMin3 (9 * C) m n := by
  unfold timeMin timeMin3
  refine Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le one_le_two ?_)
  have hA : 0 ≤ (m : ℝ) / Real.sqrt (lg m) := by positivity
  have hB : 0 ≤ (n : ℝ) * lg (lg n) / Real.sqrt (lg n) := by linarith [two_le_base hn]
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  have h : min (expM 3 m) (expN 3 n) ≤ 9 * min ((m : ℝ) / Real.sqrt (lg m)) ((n : ℝ) * lg (lg n) / Real.sqrt (lg n)) := by
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 9), expM_eq, expN_eq]
    refine min_le_min ?_ ?_
    · push_cast; linarith
    · push_cast; linarith
  calc (C : ℝ) * min (expM 3 m) (expN 3 n) ≤ (C : ℝ) * (9 * min ((m : ℝ) / Real.sqrt (lg m)) ((n : ℝ) * lg (lg n) / Real.sqrt (lg n))) :=
        mul_le_mul_of_nonneg_left h hC0
    _ = ((9 * C : ℕ) : ℝ) * min ((m : ℝ) / Real.sqrt (lg m)) ((n : ℝ) * lg (lg n) / Real.sqrt (lg n)) := by push_cast; ring

end VariableBound.Paper
