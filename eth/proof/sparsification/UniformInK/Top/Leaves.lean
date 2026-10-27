/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import UniformInK.Top.Defs
import PaddedDescent.Choice
import SparsifyWidthK.Thresholds
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # The number of leaves of the tree with the thresholds `thetaU τ`

`stLeavesU : StLeavesU`: for τ = 2^(4s+17), k ≥ 1 and s ≥ `s0U k`, the sum Σ_{j ≤ kn/τ} C(τ^(2k)·n,
j) is at most 2^(⌊n/2^s⌋+1). The estimate of the sum is
`WidthK.Thresholds.sum_choose_le_two_rpow`, which holds for every number L ≥ k in place of τ^(2k).
What is proved here is its hypothesis (k/τ)·log₂(e·τ·τ^(2k)) ≤ 1/2^s, which needs only k ≥ 1 and k²
≤ 2^s.
It is the analogue of `tauOf_works` in proof/rates/PaddedDescent/Choice.lean and of
`sum_choose_le_two_pow` in proof/rates/PaddedDescent/F/ArithWalk.lean. -/

namespace UniformInK.Leaves

open PaddedDescent

/-- k² ≤ 2^s for s ≥ s0U k. -/
public theorem sq_le_of_s0U_le {k s : ℕ} (hs : s0U k ≤ s) : k ^ 2 ≤ 2 ^ s := by
  have h1 : k ≤ 2 ^ Nat.size k := (Nat.lt_size_self k).le
  calc k ^ 2 ≤ (2 ^ Nat.size k) ^ 2 := Nat.pow_le_pow_left h1 2
    _ = 2 ^ s0U k := by rw [← pow_mul, s0U, Nat.mul_comm]
    _ ≤ 2 ^ s := Nat.pow_le_pow_right (by norm_num) hs

/-- bsumU τ k = 2^(betaU k s) for τ = 2^(4s+17). -/
public theorem bsumU_tauOf (k s : ℕ) : bsumU (tauOf s) k = 2 ^ betaU k s := by
  rw [bsumU, tauOf_pow, betaU]
  congr 1
  ring

/-- 3·τ·bsumU τ k ≤ 2^(betaU k s + 4s + 19). -/
theorem three_mul_le (k s : ℕ) : 3 * tauOf s * bsumU (tauOf s) k ≤ 2 ^ (betaU k s + 4 * s + 19) := by
  rw [bsumU_tauOf, tauOf]
  calc 3 * 2 ^ (4 * s + 17) * 2 ^ betaU k s ≤ 2 ^ 2 * 2 ^ (4 * s + 17) * 2 ^ betaU k s :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))
    _ = 2 ^ (betaU k s + 4 * s + 19) := by rw [← pow_add, ← pow_add]; congr 1; omega

/-- k·(betaU k s + 4s + 19)·2^s ≤ τ, if 1 ≤ k and k² ≤ 2^s: the left side is at most 4k²·(4s+17)·2^s
≤ 68·2^(3s). -/
theorem mul_exponent_le {k s : ℕ} (hk : 1 ≤ k) (hs : k ^ 2 ≤ 2 ^ s) : k * (betaU k s + 4 * s + 19) * 2 ^ s ≤ tauOf s := by
  have h1 : s + 1 ≤ 2 ^ s := Nat.lt_two_pow_self
  have h2 : 4 * s + 17 ≤ 17 * 2 ^ s := by omega
  have h3 : k * (betaU k s + 4 * s + 19) ≤ 4 * k ^ 2 * (4 * s + 17) := by
    unfold betaU
    nlinarith [Nat.mul_le_mul hk hk, Nat.mul_le_mul_right s (Nat.mul_le_mul hk hk), Nat.mul_le_mul_left k hk, Nat.mul_le_mul_right s (Nat.mul_le_mul_left k hk)]
  calc k * (betaU k s + 4 * s + 19) * 2 ^ s ≤ 4 * 2 ^ s * (17 * 2 ^ s) * 2 ^ s :=
        Nat.mul_le_mul_right _ (h3.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ hs) h2))
    _ = 68 * 2 ^ (3 * s) := by rw [show 3 * s = s + s + s by ring, pow_add, pow_add]; ring
    _ ≤ 2 ^ (s + 17) * 2 ^ (3 * s) := Nat.mul_le_mul_right _ (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left 17 s)))
    _ = tauOf s := by rw [tauOf, ← pow_add]; congr 1; omega

/-- (k/τ)·log₂(e·τ·bsumU τ k) ≤ 1/2^s for τ = 2^(4s+17), 1 ≤ k and s ≥ s0U k. -/
theorem tauOf_worksU {k s : ℕ} (hk : 1 ≤ k) (hs : s0U k ≤ s) :
    ((k : ℝ) / (tauOf s : ℝ)) * Real.logb 2 (Real.exp 1 * (tauOf s : ℝ) * (bsumU (tauOf s) k : ℝ)) ≤ 1 / 2 ^ s := by
  have hτ0 : (0 : ℝ) < (tauOf s : ℝ) := by exact_mod_cast lt_of_lt_of_le (by norm_num) (two_le_tauOf s)
  have hb0 : (0 : ℝ) < (bsumU (tauOf s) k : ℝ) := by
    rw [bsumU_tauOf]
    exact_mod_cast Nat.two_pow_pos _
  have he : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  have h3 : (3 : ℝ) * (tauOf s : ℝ) * (bsumU (tauOf s) k : ℝ) ≤ (2 : ℝ) ^ (betaU k s + 4 * s + 19) := by
    exact_mod_cast three_mul_le k s
  have hle : Real.exp 1 * (tauOf s : ℝ) * (bsumU (tauOf s) k : ℝ) ≤ (2 : ℝ) ^ (betaU k s + 4 * s + 19) :=
    le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he hτ0.le) hb0.le) h3
  have hlogb : Real.logb 2 (Real.exp 1 * (tauOf s : ℝ) * (bsumU (tauOf s) k : ℝ)) ≤ ((betaU k s + 4 * s + 19 : ℕ) : ℝ) := by
    have hpos : 0 < Real.exp 1 * (tauOf s : ℝ) * (bsumU (tauOf s) k : ℝ) := mul_pos (mul_pos (Real.exp_pos 1) hτ0) hb0
    calc Real.logb 2 (Real.exp 1 * (tauOf s : ℝ) * (bsumU (tauOf s) k : ℝ)) ≤ Real.logb 2 ((2 : ℝ) ^ (betaU k s + 4 * s + 19)) :=
          Real.logb_le_logb_of_le one_lt_two hpos hle
      _ = ((betaU k s + 4 * s + 19 : ℕ) : ℝ) := by rw [Real.logb_pow, Real.logb_self_eq_one one_lt_two, mul_one]
  have h2s : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
  have hnat : k * (betaU k s + 4 * s + 19) * 2 ^ s ≤ 1 * tauOf s := by
    rw [one_mul]
    exact mul_exponent_le hk (sq_le_of_s0U_le hs)
  calc ((k : ℝ) / (tauOf s : ℝ)) * Real.logb 2 (Real.exp 1 * (tauOf s : ℝ) * (bsumU (tauOf s) k : ℝ))
      ≤ ((k : ℝ) / (tauOf s : ℝ)) * ((betaU k s + 4 * s + 19 : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hlogb (div_nonneg (Nat.cast_nonneg k) hτ0.le)
    _ ≤ 1 / 2 ^ s := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hτ0 h2s]
        exact_mod_cast hnat

/-- k ≤ bsumU τ k for τ = 2^(4s+17). -/
theorem le_bsumU (k s : ℕ) : k ≤ bsumU (tauOf s) k := by
  rw [bsumU_tauOf]
  refine Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by norm_num) ?_)
  unfold betaU
  nlinarith

end UniformInK.Leaves

namespace UniformInK

open PaddedDescent UniformInK.Leaves

/-- Σ_{j ≤ kn/τ} C(bsumU τ k · n, j) ≤ 2^(⌊n/2^s⌋+1) for τ = 2^(4s+17), k ≥ 1 and s ≥ s0U k. -/
public theorem stLeavesU : StLeavesU := by
  intro k n s hk hs
  have h1 := WidthK.Thresholds.sum_choose_le_two_rpow (one_le_tauOf s) (le_bsumU k s) (tauOf_worksU hk hs) n
  have h2 : n < 2 ^ s * (n / 2 ^ s + 1) := Nat.lt_mul_div_succ n (by positivity)
  have h3 : (n : ℝ) ≤ (2 : ℝ) ^ s * ((n / 2 ^ s + 1 : ℕ) : ℝ) := by exact_mod_cast h2.le
  have h4 : (1 : ℝ) / 2 ^ s * (n : ℝ) ≤ ((n / 2 ^ s + 1 : ℕ) : ℝ) := by
    have hp : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
    rw [one_div, inv_mul_le_iff₀ hp]
    exact h3
  have h5 : ((∑ j ∈ Finset.range (k * n / tauOf s + 1), (bsumU (tauOf s) k * n).choose j : ℕ) : ℝ) ≤ ((2 ^ (n / 2 ^ s + 1) : ℕ) : ℝ) := by
    calc ((∑ j ∈ Finset.range (k * n / tauOf s + 1), (bsumU (tauOf s) k * n).choose j : ℕ) : ℝ)
        ≤ (2 : ℝ) ^ (1 / 2 ^ s * (n : ℝ)) := h1
      _ ≤ (2 : ℝ) ^ (((n / 2 ^ s + 1 : ℕ) : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h4
      _ = ((2 ^ (n / 2 ^ s + 1) : ℕ) : ℝ) := by rw [Real.rpow_natCast]; push_cast; ring
  exact_mod_cast h5

end UniformInK
