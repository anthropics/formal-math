/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsifyWidthK.Interfaces
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import all StepMachines.Math.SparsifyCount
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-! # The thresholds of the sparsification of a k-CNF, and the number of leaves of its tree

The thresholds θ i and the bounds β i are defined in `SparsifyWidthK/Defs.lean` by one recursion
from a single number τ. This file proves the equations and
inequalities between them that the count of the steps of a path needs, the bound 2 + β 1 + … + β i ≤
τ^(2^(i+1)) for τ ≥ 4, the estimate
Σ_{j ≤ kn/τ} C(L·n, j) ≤ 2^(εn) for the number of leaves, and that for every k and every ε > 0 a
suitable τ exists. At the end these facts are given in
the form of the interface statements `StThr`, `StBetaSum`, `StLeafCount` and `StExistsTau` of
`SparsifyWidthK/Interfaces.lean`.
The estimate uses the lemma `pow_mul_sum_choose_le_exp` of `StepMachines/Math/SparsifyCount.lean`. -/

public section

namespace WidthK.Thresholds

open Finset

/-! ### The defining equations

Below, θ i stands for `theta τ i`, β i for `beta τ i`, and `bsum τ i` is the sum 2 + β 1 + … + β i. -/

/-- θ 0 = 1. -/
theorem theta_zero (τ : ℕ) : theta τ 0 = 1 := rfl

/-- The sum 2 + β 1 + … + β i is 2 for i = 0. -/
theorem bsum_zero (τ : ℕ) : bsum τ 0 = 2 := rfl

/-- The recursion for θ as it is written in the definition. -/
theorem theta_succ' (τ i : ℕ) : theta τ (i + 1) = 2 * τ * theta τ i * bsum τ i := rfl

/-- The recursion for the sum as it is written in the definition. -/
theorem bsum_succ' (τ i : ℕ) : bsum τ (i + 1) = bsum τ i * (1 + 2 * theta τ i) := rfl

/-- β 0 = 0. -/
theorem beta_zero (τ : ℕ) : beta τ 0 = 0 := rfl

/-- β (i+1) = 2 · θ i · (2 + β 1 + … + β i). -/
theorem beta_succ (τ i : ℕ) : beta τ (i + 1) = 2 * theta τ i * bsum τ i := rfl

/-- θ (i+1) = τ · β (i+1). -/
theorem theta_succ (τ i : ℕ) : theta τ (i + 1) = τ * beta τ (i + 1) := by
  rw [theta_succ', beta_succ]; ring

/-- Each step of the recursion adds β (i+1) to the sum. -/
theorem bsum_succ (τ i : ℕ) : bsum τ (i + 1) = bsum τ i + beta τ (i + 1) := by
  rw [bsum_succ', beta_succ]; ring

/-- `bsum τ i` is indeed 2 + β 0 + β 1 + … + β i (and β 0 = 0). -/
theorem bsum_eq (τ i : ℕ) : bsum τ i = 2 + ∑ j ∈ range (i + 1), beta τ j := by
  induction i with
  | zero => simp [bsum_zero, beta_zero]
  | succ i ih => rw [bsum_succ, ih, sum_range_succ _ (i + 1)]; ring

/-! ### Inequalities between the thresholds -/

/-- The sum is at least 2. -/
theorem two_le_bsum (τ i : ℕ) : 2 ≤ bsum τ i := by rw [bsum_eq]; omega

/-- Every threshold is positive, if τ is. -/
theorem one_le_theta {τ : ℕ} (hτ : 1 ≤ τ) (i : ℕ) : 1 ≤ theta τ i := by
  induction i with
  | zero => exact le_refl _
  | succ i ih =>
    rw [theta_succ']
    have := two_le_bsum τ i
    exact Nat.one_le_iff_ne_zero.2 (by positivity)

/-- The sum grows by at least 1 with each step: i + 2 ≤ 2 + β 1 + … + β i. -/
theorem add_two_le_bsum {τ : ℕ} (hτ : 1 ≤ τ) (i : ℕ) : i + 2 ≤ bsum τ i := by
  induction i with
  | zero => exact le_refl _
  | succ i ih =>
    have h1 := one_le_theta hτ i
    have h2 : 1 ≤ beta τ (i + 1) := by
      rw [beta_succ]
      have := two_le_bsum τ i
      exact Nat.one_le_iff_ne_zero.2 (by positivity)
    rw [bsum_succ]; omega

/-- 2 + β 1 + … + β i ≤ 2 · θ i. -/
theorem bsum_le {τ : ℕ} (hτ : 1 ≤ τ) (i : ℕ) : bsum τ i ≤ 2 * theta τ i := by
  cases i with
  | zero => exact le_refl _
  | succ i =>
    have h1 := one_le_theta hτ i
    rw [bsum_succ', theta_succ']
    calc bsum τ i * (1 + 2 * theta τ i) ≤ bsum τ i * (4 * τ * theta τ i) := by
          refine Nat.mul_le_mul_left _ ?_
          have : 4 * 1 * theta τ i ≤ 4 * τ * theta τ i :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hτ)
          omega
      _ = 2 * (2 * τ * theta τ i * bsum τ i) := by ring

/-- τ² · θ i ≤ τ^(2^(i+1)) for τ ≥ 4: by the previous lemma the quantity τ² · θ i is at most squared
in each step. -/
theorem sq_mul_theta_le {τ : ℕ} (hτ : 4 ≤ τ) (i : ℕ) : τ ^ 2 * theta τ i ≤ τ ^ 2 ^ (i + 1) := by
  induction i with
  | zero => simp [theta_zero]
  | succ i ih =>
    have hb := bsum_le (by omega : 1 ≤ τ) i
    calc τ ^ 2 * theta τ (i + 1) = τ ^ 2 * (2 * τ * theta τ i * bsum τ i) := by rw [theta_succ']
      _ ≤ τ ^ 2 * (2 * τ * theta τ i * (2 * theta τ i)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hb)
      _ = 4 * (τ ^ 3 * theta τ i ^ 2) := by ring
      _ ≤ τ * (τ ^ 3 * theta τ i ^ 2) := Nat.mul_le_mul_right _ hτ
      _ = (τ ^ 2 * theta τ i) ^ 2 := by ring
      _ ≤ (τ ^ 2 ^ (i + 1)) ^ 2 := Nat.pow_le_pow_left ih 2
      _ = τ ^ 2 ^ (i + 1 + 1) := by rw [← pow_mul, ← pow_succ]

/-- 2 + β 1 + … + β i ≤ τ^(2^(i+1)) for τ ≥ 4. -/
theorem bsum_le_pow {τ : ℕ} (hτ : 4 ≤ τ) (i : ℕ) : bsum τ i ≤ τ ^ 2 ^ (i + 1) := by
  refine le_trans (bsum_le (by omega) i) (le_trans (Nat.mul_le_mul_right _ ?_) (sq_mul_theta_le hτ i))
  nlinarith

/-! ### The number of leaves -/

open Groundwork.Sparsify in
/-- If (k/τ)·log₂(e·τ·L) ≤ ε, with k ≤ L and 1 ≤ τ, then Σ_{j ≤ kn/τ} C(L·n, j) ≤ 2^(εn). -/
theorem sum_choose_le_two_rpow {k τ L : ℕ} (hτ : 1 ≤ τ) (hkL : k ≤ L) {ε : ℝ}
    (h : ((k : ℝ) / (τ : ℝ)) * Real.logb 2 (Real.exp 1 * (τ : ℝ) * (L : ℝ)) ≤ ε) (n : ℕ) :
    ((∑ j ∈ range (k * n / τ + 1), (L * n).choose j : ℕ) : ℝ) ≤ (2 : ℝ) ^ (ε * (n : ℝ)) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hε : 0 ≤ ε := by simpa using h
    simp only [zero_mul, Nat.zero_div, zero_add, range_one, Finset.sum_singleton, Nat.choose_zero_right,
      Nat.cast_one]
    exact Real.one_le_rpow one_le_two (by positivity)
  have ht0 : (0 : ℝ) < (τ : ℝ) := by exact_mod_cast hτ
  have ht1 : (1 : ℝ) ≤ (τ : ℝ) := by exact_mod_cast hτ
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkL' : (k : ℝ) ≤ (L : ℝ) := by exact_mod_cast hkL
  have hL0 : (0 : ℝ) < (L : ℝ) := by linarith
  set S : ℝ := ((∑ j ∈ range (k * n / τ + 1), (L * n).choose j : ℕ) : ℝ) with hS
  set b : ℝ := (τ : ℝ) * (L : ℝ) / (k : ℝ) with hb
  set ρ : ℝ := (k : ℝ) * (n : ℝ) / (τ : ℝ) with hρ
  have hb1 : 1 ≤ b := by
    rw [hb, le_div_iff₀ hk0]; nlinarith
  have hb0 : 0 < b := by linarith
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hr : k * n / τ ≤ L * n :=
    le_trans (Nat.div_le_self _ _) (Nat.mul_le_mul_right _ hkL)
  have hrρ : ((k * n / τ : ℕ) : ℝ) ≤ ρ := by
    have := @Nat.cast_div_le ℝ _ _ _ (k * n) τ
    rw [hρ]; push_cast at this; exact this
  have hkey : b⁻¹ ^ (k * n / τ) * S ≤ Real.exp ρ := by
    have hx : ((L * n : ℕ) : ℝ) * b⁻¹ = ρ := by
      rw [hb, hρ]; push_cast; field_simp
    rw [← hx]
    exact pow_mul_sum_choose_le_exp (inv_pos.mpr hb0) (inv_le_one_of_one_le₀ hb1) hr
  have hS1 : S ≤ b ^ (k * n / τ) * Real.exp ρ := by
    rw [inv_pow] at hkey
    have hp : 0 < b ^ (k * n / τ) := by positivity
    calc S = b ^ (k * n / τ) * ((b ^ (k * n / τ))⁻¹ * S) := by field_simp
      _ ≤ b ^ (k * n / τ) * Real.exp ρ := mul_le_mul_of_nonneg_left hkey hp.le
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hy : 0 < Real.exp 1 * (τ : ℝ) * (L : ℝ) := by positivity
  calc S ≤ b ^ (k * n / τ) * Real.exp ρ := hS1
    _ = b ^ ((k * n / τ : ℕ) : ℝ) * Real.exp ρ := by rw [Real.rpow_natCast]
    _ ≤ b ^ ρ * Real.exp ρ :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hb1 hrρ) (Real.exp_pos ρ).le
    _ = (b * Real.exp 1) ^ ρ := by rw [Real.mul_rpow hb0.le he.le, Real.exp_one_rpow]
    _ ≤ (Real.exp 1 * (τ : ℝ) * (L : ℝ)) ^ ρ := by
        refine Real.rpow_le_rpow (by positivity) ?_ hρ0
        have : b ≤ (τ : ℝ) * (L : ℝ) := by
          rw [hb]; exact div_le_self (by positivity) hk1
        nlinarith
    _ = (2 : ℝ) ^ (Real.logb 2 (Real.exp 1 * (τ : ℝ) * (L : ℝ)) * ρ) := by
        rw [Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) hy]
    _ ≤ (2 : ℝ) ^ (ε * (n : ℝ)) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        calc Real.logb 2 (Real.exp 1 * (τ : ℝ) * (L : ℝ)) * ρ
            = ((k : ℝ) / (τ : ℝ)) * Real.logb 2 (Real.exp 1 * (τ : ℝ) * (L : ℝ)) * (n : ℝ) := by rw [hρ]; ring
          _ ≤ ε * (n : ℝ) := mul_le_mul_of_nonneg_right h hn

/-- For every k, every ε > 0 and every τ₀ there is a number τ ≥ τ₀, τ ≥ 4, with (k/τ)·log₂(e·τ·(2 +
β 1 + … + β k)) ≤ ε.
The proof takes τ = m² with m ≥ 4·k·(2^(k+1)+1)/ε and uses log m ≤ m − 1. -/
theorem exists_tau (k τ₀ : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℕ, τ₀ ≤ τ ∧ 4 ≤ τ ∧
      ((k : ℝ) / (τ : ℝ)) * Real.logb 2 (Real.exp 1 * (τ : ℝ) * (bsum τ k : ℝ)) ≤ ε := by
  set E : ℕ := 2 ^ (k + 1) + 1 with hE
  obtain ⟨m₀, hm₀⟩ := exists_nat_ge (4 * (k : ℝ) * (E : ℝ) / ε)
  set m : ℕ := max (max 2 τ₀) m₀ with hm
  have hm2 : 2 ≤ m := le_trans (le_max_left _ _) (le_max_left _ _)
  have hmτ : τ₀ ≤ m := le_trans (le_max_right _ _) (le_max_left _ _)
  have hmr2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hmε : 4 * (k : ℝ) * (E : ℝ) / ε ≤ (m : ℝ) := hm₀.trans (by exact_mod_cast le_max_right _ m₀)
  have hmε' : 4 * (k : ℝ) * (E : ℝ) ≤ ε * (m : ℝ) := by
    rw [div_le_iff₀ hε] at hmε; linarith
  have h4 : 4 ≤ m ^ 2 := by nlinarith
  refine ⟨m ^ 2, le_trans hmτ (Nat.le_self_pow (by norm_num) _), h4, ?_⟩
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
  have hE1 : (1 : ℝ) ≤ (E : ℝ) := by
    rw [hE]; push_cast; have : (0 : ℝ) < 2 ^ (k + 1) := by positivity
    linarith
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at this ⊢; linarith
  have hlogm : Real.log (m : ℝ) ≤ (m : ℝ) - 1 := Real.log_le_sub_one_of_pos hm0
  have hB : (bsum (m ^ 2) k : ℝ) ≤ ((m ^ 2 : ℕ) : ℝ) ^ 2 ^ (k + 1) := by
    exact_mod_cast bsum_le_pow h4 k
  have hB0 : (0 : ℝ) < (bsum (m ^ 2) k : ℝ) := by
    have := two_le_bsum (m ^ 2) k
    exact_mod_cast (by omega : 0 < bsum (m ^ 2) k)
  have hle : Real.exp 1 * ((m ^ 2 : ℕ) : ℝ) * (bsum (m ^ 2) k : ℝ) ≤ Real.exp 1 * (m : ℝ) ^ (2 * E) := by
    have e1 : Real.exp 1 * (m : ℝ) ^ (2 * E) = Real.exp 1 * ((m ^ 2 : ℕ) : ℝ) * ((m ^ 2 : ℕ) : ℝ) ^ 2 ^ (k + 1) := by
      rw [hE]; push_cast; ring
    rw [e1]
    exact mul_le_mul_of_nonneg_left hB (by positivity)
  have hlog : Real.log (Real.exp 1 * ((m ^ 2 : ℕ) : ℝ) * (bsum (m ^ 2) k : ℝ)) ≤ 2 * (E : ℝ) * (m : ℝ) := by
    have hpos : 0 < Real.exp 1 * ((m ^ 2 : ℕ) : ℝ) * (bsum (m ^ 2) k : ℝ) := by positivity
    refine le_trans (Real.log_le_log hpos hle) ?_
    rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp, Real.log_pow]
    push_cast
    nlinarith
  have hlogb : Real.logb 2 (Real.exp 1 * ((m ^ 2 : ℕ) : ℝ) * (bsum (m ^ 2) k : ℝ)) ≤ 4 * (E : ℝ) * (m : ℝ) := by
    rw [← Real.log_div_log, div_le_iff₀ (by linarith)]
    have : 0 ≤ (E : ℝ) * (m : ℝ) := by positivity
    nlinarith
  calc ((k : ℝ) / ((m ^ 2 : ℕ) : ℝ)) * Real.logb 2 (Real.exp 1 * ((m ^ 2 : ℕ) : ℝ) * (bsum (m ^ 2) k : ℝ))
      ≤ ((k : ℝ) / ((m ^ 2 : ℕ) : ℝ)) * (4 * (E : ℝ) * (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogb (by positivity)
    _ = 4 * (k : ℝ) * (E : ℝ) / (m : ℝ) := by push_cast; field_simp
    _ ≤ ε := by rw [div_le_iff₀ hm0]; exact hmε'

end WidthK.Thresholds

/-! ### The four interface statements -/

namespace WidthK

open Finset Thresholds

/-- The thresholds θ and the bounds β have the three properties that the count of the steps of a
path uses. -/
theorem stThr : StThr := by
  intro τ hτ
  refine ⟨fun i => one_le_theta hτ i, fun i => ?_, fun r => ?_⟩
  · rw [← bsum_eq, beta_succ]
  · cases r with
    | zero => simp [beta_zero]
    | succ r => rw [theta_succ]

/-- β 0 + … + β (k-1) ≤ 2 + β 1 + … + β k. -/
theorem stBetaSum : StBetaSum := by
  intro τ k
  rw [bsum_eq, sum_range_succ]
  omega

/-- The number of leaves of the tree is at most 2^(εn), if (k/τ)·log₂(e·τ·(2 + β 1 + … + β k)) ≤ ε. -/
theorem stLeafCount : StLeafCount := by
  intro k τ ε hτ h n
  exact sum_choose_le_two_rpow hτ (by have := add_two_le_bsum hτ k; omega) h n

/-- For every k and every ε > 0 there are arbitrarily large τ with (k/τ)·log₂(e·τ·(2 + β 1 + … + β
k)) ≤ ε. -/
theorem stExistsTau : StExistsTau := fun k τ₀ _ hε => exists_tau k τ₀ hε

end WidthK
