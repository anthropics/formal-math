/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.TopN.Defs
import all ClauseBound.TopN.Arith
import ClauseBound.Alg.TopArith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-! # The master inequality W ≤ A₁·K·e, between real numbers

This file proves the master inequality `master`, with its constants `cK`, `qE`, `a0`, `A1` and the
bound `D_le`, and defines the slope `ckN` and proves the estimate `le_of_small`. -/

namespace ClauseBound.TopN.Arith

open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith

/-! ### The master inequality: W ≤ A₁·K·e -/

/-- 2^(k+1) + 1, the slope of β in 4s + 17. -/
def cK (k : ℕ) : ℕ := 2 ^ (k + 1) + 1

/-- The power of log₂ K that bounds W/e. -/
def qE (k C C₀ : ℕ) : ℕ := 12 * cK k * C * C₀ + C₀ + 1

/-- The constant in D ≤ a₀·(log₂ K)^(4·c·C·C₀). -/
def a0 (k C : ℕ) : ℕ := 2 ^ (17 * cK k + k + 3) * 2 ^ (4 * cK k * C)

/-- The constant of the master inequality. -/
def A1 (k C C₀ : ℕ) : ℕ := 2 * a0 k C ^ 3 * ((qE k C C₀).factorial * 2 ^ qE k C C₀)

/-- D = 2^β is at most a constant times a power of log₂ K. -/
theorem D_le {K s C C₀ k : ℕ} {e : ℝ} (hK : 2 ≤ K) (he : 1 / Real.logb 2 K ^ C₀ ≤ e) (h2 : (2 : ℝ) ^ s ≤ (2 / e) ^ C) :
    ((2 ^ betaN k s : ℕ) : ℝ) ≤ (a0 k C : ℝ) * Real.logb 2 K ^ (4 * cK k * C * C₀) := by
  have hy1 : (1 : ℝ) ≤ Real.logb 2 K := by simpa using le_logb_of_pow_le K 1 (by simpa using hK)
  generalize Real.logb 2 K = y at he hy1 ⊢
  have hy0 : 0 < y := by linarith
  have hyC : 0 < y ^ C₀ := by positivity
  have he0 : 0 < e := lt_of_lt_of_le (by positivity) he
  have h1e : 1 ≤ e * y ^ C₀ := by rwa [div_le_iff₀ hyC] at he
  have h2e : 2 / e ≤ 2 * y ^ C₀ := by
    rw [div_le_iff₀ he0]
    nlinarith
  have hs : (2 : ℝ) ^ s ≤ (2 * y ^ C₀) ^ C := h2.trans (pow_le_pow_left₀ (by positivity) h2e C)
  have eβ : betaN k s = s * (4 * cK k) + (17 * cK k + k + 3) := by unfold betaN cK; ring
  calc ((2 ^ betaN k s : ℕ) : ℝ) = ((2 : ℝ) ^ s) ^ (4 * cK k) * 2 ^ (17 * cK k + k + 3) := by
        rw [eβ]; push_cast; rw [pow_add, pow_mul]
    _ ≤ ((2 * y ^ C₀) ^ C) ^ (4 * cK k) * 2 ^ (17 * cK k + k + 3) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hs _) (by positivity)
    _ = (a0 k C : ℝ) * y ^ (4 * cK k * C * C₀) := by
        have e1 : C * (4 * cK k) = 4 * cK k * C := by ring
        have e2 : C₀ * (4 * cK k * C) = 4 * cK k * C * C₀ := by ring
        unfold a0
        push_cast
        rw [← pow_mul, mul_pow, ← pow_mul, e1, e2]
        ring

/-- W ≤ A₁·K·e. -/
theorem master {K s C C₀ k : ℕ} {e : ℝ} (hK : 2 ≤ K) (he : 1 / Real.logb 2 K ^ C₀ ≤ e) (h2 : (2 : ℝ) ^ s ≤ (2 / e) ^ C) :
    ((Wof k K s : ℕ) : ℝ) ≤ (A1 k C C₀ : ℝ) * K * e := by
  have hD := D_le (k := k) hK he h2
  have hY : (K.size : ℝ) ≤ 2 * Real.logb 2 K := size_le_two_logb K hK
  have hq := logb_pow_le K (qE k C C₀) hK
  have hy1 : (1 : ℝ) ≤ Real.logb 2 K := by simpa using le_logb_of_pow_le K 1 (by simpa using hK)
  have hA : (A1 k C C₀ : ℝ) = 2 * (a0 k C : ℝ) ^ 3 * (((qE k C C₀).factorial * 2 ^ qE k C C₀ : ℕ) : ℝ) := by
    unfold A1; push_cast; ring
  have hqe : qE k C C₀ = 3 * (4 * cK k * C * C₀) + 1 + C₀ := by unfold qE; ring
  rw [hA]
  generalize (((qE k C C₀).factorial * 2 ^ qE k C C₀ : ℕ) : ℝ) = F at hq ⊢
  rw [hqe] at hq
  generalize 4 * cK k * C * C₀ = p at hD hq
  generalize Real.logb 2 K = y at he hy1 hD hY hq
  have hy0 : 0 < y := by linarith
  have hyC : 0 < y ^ C₀ := by positivity
  have he0 : 0 < e := lt_of_lt_of_le (by positivity) he
  have h1e : 1 ≤ e * y ^ C₀ := by rwa [div_le_iff₀ hyC] at he
  have hb : ((betaN k s + 3 : ℕ) : ℝ) ≤ ((2 ^ betaN k s : ℕ) : ℝ) := by exact_mod_cast b_le_D k s
  have hW0 : ((Wof k K s : ℕ) : ℝ) = ((betaN k s + 3 : ℕ) : ℝ) ^ 2 * ((2 ^ betaN k s : ℕ) : ℝ) * (K.size : ℝ) := by
    unfold Wof; push_cast; ring
  rw [hW0]
  have hb0 : (0 : ℝ) ≤ ((betaN k s + 3 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hD0 : (0 : ℝ) ≤ ((2 ^ betaN k s : ℕ) : ℝ) := Nat.cast_nonneg _
  have hY0 : (0 : ℝ) ≤ (K.size : ℝ) := Nat.cast_nonneg _
  have ha0 : (0 : ℝ) ≤ (a0 k C : ℝ) := Nat.cast_nonneg _
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
  generalize ((betaN k s + 3 : ℕ) : ℝ) = b at hb hb0 ⊢
  generalize ((2 ^ betaN k s : ℕ) : ℝ) = D at hb hD hD0 ⊢
  generalize (K.size : ℝ) = Y at hY hY0 ⊢
  generalize (a0 k C : ℝ) = a at hD ha0 ⊢
  calc b ^ 2 * D * Y ≤ D ^ 2 * D * (2 * y) := by gcongr
    _ = D ^ 3 * (2 * y) := by ring
    _ ≤ (a * y ^ p) ^ 3 * (2 * y) := by gcongr
    _ = 2 * a ^ 3 * y ^ (3 * p + 1) * 1 := by ring
    _ ≤ 2 * a ^ 3 * y ^ (3 * p + 1) * (e * y ^ C₀) := mul_le_mul_of_nonneg_left h1e (by positivity)
    _ = 2 * a ^ 3 * y ^ (3 * p + 1 + C₀) * e := by ring
    _ ≤ 2 * a ^ 3 * (F * K) * e := by gcongr
    _ = 2 * a ^ 3 * F * K * e := by ring

/-! ### The exponent -/

/-- The slope of b = β + 3 in s + 1. -/
def ckN (k : ℕ) : ℕ := 17 * (2 ^ (k + 1) + 1) + k + 6

/-! ### An estimate -/

/-- If s is below a bound t and 2^(−s) ≤ e, then n ≤ 2^t·(n·e). -/
theorem le_of_small {s t n : ℕ} {e : ℝ} (hst : s ≤ t) (g1 : 1 / (2 : ℝ) ^ s ≤ e) : (n : ℝ) ≤ ((2 ^ t : ℕ) : ℝ) * ((n : ℝ) * e) := by
  have a1 : (2 : ℝ) ^ s ≤ (2 : ℝ) ^ t := pow_le_pow_right₀ (by norm_num) hst
  have a2 : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
  have a3 : 1 ≤ e * (2 : ℝ) ^ s := by rwa [div_le_iff₀ a2] at g1
  have he0 : 0 ≤ e := le_trans (by positivity) g1
  have h3 : (1 : ℝ) ≤ (2 : ℝ) ^ t * e := by
    have := mul_le_mul_of_nonneg_left a1 he0
    linarith
  push_cast
  calc (n : ℝ) = n * 1 := (mul_one _).symm
    _ ≤ n * ((2 : ℝ) ^ t * e) := mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg n)
    _ = (2 : ℝ) ^ t * ((n : ℝ) * e) := by ring

end ClauseBound.TopN.Arith
