/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.TopN.Defs
import ClauseBound.Alg.End
import WidthK.Decode
import CountKSat.InOut

/-! # Arithmetic for time bounds in the number n of variables

Inequalities of real arithmetic for bounds of the form C·2^(C·X) with X = n·r. `time_le'`: if L + 1
≤ a·2^(H·X) and E ≤ G·X, then q·(L + 2^E + 1)^q ≤ C·2^(C·X)
with C = q·(a+1)^q + q·(H + G). `log_le_mul`: if r ≥ 1/(c·(log₂(n+2))^c) with c ≥ 1 and n ≥ 1, then
log₂(n+2) ≤ c·D·(n·r) with D = 3·(c+1)!·2^(c+1). -/

public section

namespace ClauseBound.TopN.End

open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.Alg.End

/-- log₂(n+2) ≤ c·D·(n·r), where D = 3·(c+1)!·2^(c+1), if r ≥ 1/(c·(log₂(n+2))^c) and n ≥ 1. -/
theorem log_le_mul {c n : ℕ} {r : ℝ} (hc : 1 ≤ c) (hn : 1 ≤ n) (h : 1 / ((c : ℝ) * Real.logb 2 ((n : ℝ) + 2) ^ c) ≤ r) :
    Real.logb 2 ((n : ℝ) + 2) ≤ ((c * (3 * (c + 1).factorial * 2 ^ (c + 1)) : ℕ) : ℝ) * ((n : ℝ) * r) := by
  have hy := one_le_log n
  have h1 := one_le_mul_of_div_le hc hy h
  have h2 := log_pow_le (c + 1) hn
  set y := Real.logb 2 ((n : ℝ) + 2) with hyd
  set D : ℕ := 3 * (c + 1).factorial * 2 ^ (c + 1)
  have hr : 0 ≤ r := le_trans (by positivity) h
  calc y = y * 1 := (mul_one y).symm
    _ ≤ y * ((c : ℝ) * y ^ c * r) := mul_le_mul_of_nonneg_left h1 (by linarith)
    _ = (c : ℝ) * r * y ^ (c + 1) := by ring
    _ ≤ (c : ℝ) * r * ((D : ℝ) * n) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = ((c * D : ℕ) : ℝ) * ((n : ℝ) * r) := by push_cast; ring

/-- If L + 1 ≤ a·2^(H·X) and E ≤ G·X then q·(L + 2^E + 1)^q ≤ C·2^(C·X) with C = q·(a+1)^q + q·(H +
G). -/
theorem time_le' (q L E a H G : ℕ) {X : ℝ} (hX : 0 ≤ X) (hL : ((L + 1 : ℕ) : ℝ) ≤ (a : ℝ) * (2 : ℝ) ^ ((H : ℝ) * X)) (hE : (E : ℝ) ≤ (G : ℝ) * X) :
    ((q * (L + 2 ^ E + 1) ^ q : ℕ) : ℝ) ≤
      ((q * (a + 1) ^ q + q * (H + G) : ℕ) : ℝ) * (2 : ℝ) ^ (((q * (a + 1) ^ q + q * (H + G) : ℕ) : ℝ) * X) := by
  have e2 : ((2 : ℝ) ^ E) ≤ (2 : ℝ) ^ ((G : ℝ) * X) := by
    rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hE
  have m1 : (2 : ℝ) ^ ((H : ℝ) * X) ≤ (2 : ℝ) ^ (((H + G : ℕ) : ℝ) * X) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_add_right _ _) hX)
  have m2 : (2 : ℝ) ^ ((G : ℝ) * X) ≤ (2 : ℝ) ^ (((H + G : ℕ) : ℝ) * X) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_add_left _ _) hX)
  have h3 : ((L + 2 ^ E + 1 : ℕ) : ℝ) ≤ ((a + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (((H + G : ℕ) : ℝ) * X) := by
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    calc ((L + 2 ^ E + 1 : ℕ) : ℝ) = ((L + 1 : ℕ) : ℝ) + (2 : ℝ) ^ E := by push_cast; ring
      _ ≤ (a : ℝ) * (2 : ℝ) ^ ((H : ℝ) * X) + (2 : ℝ) ^ ((G : ℝ) * X) := add_le_add hL e2
      _ ≤ (a : ℝ) * (2 : ℝ) ^ (((H + G : ℕ) : ℝ) * X) + (2 : ℝ) ^ (((H + G : ℕ) : ℝ) * X) := add_le_add (mul_le_mul_of_nonneg_left m1 ha0) m2
      _ = ((a + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (((H + G : ℕ) : ℝ) * X) := by push_cast; ring
  have h4 : ((2 : ℝ) ^ (((H + G : ℕ) : ℝ) * X)) ^ q = (2 : ℝ) ^ (((q * (H + G) : ℕ) : ℝ) * X) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; congr 1; push_cast; ring
  have h5 : (2 : ℝ) ^ (((q * (H + G) : ℕ) : ℝ) * X) ≤ (2 : ℝ) ^ (((q * (a + 1) ^ q + q * (H + G) : ℕ) : ℝ) * X) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_right ?_ hX)
    exact_mod_cast Nat.le_add_left _ _
  have h6 : ((q * (a + 1) ^ q : ℕ) : ℝ) ≤ ((q * (a + 1) ^ q + q * (H + G) : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right _ _
  calc ((q * (L + 2 ^ E + 1) ^ q : ℕ) : ℝ) = (q : ℝ) * ((L + 2 ^ E + 1 : ℕ) : ℝ) ^ q := by push_cast; ring
    _ ≤ (q : ℝ) * (((a + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (((H + G : ℕ) : ℝ) * X)) ^ q :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h3 q) (by positivity)
    _ = ((q * (a + 1) ^ q : ℕ) : ℝ) * (2 : ℝ) ^ (((q * (H + G) : ℕ) : ℝ) * X) := by rw [mul_pow, h4]; push_cast; ring
    _ ≤ _ := mul_le_mul h6 h5 (by positivity) (by positivity)

end ClauseBound.TopN.End
