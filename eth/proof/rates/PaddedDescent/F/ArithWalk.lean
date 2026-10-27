/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.Choice
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FieldSimp

/-! The number of leaves of the sparsification tree for clauses of width k, as a power of two with a
natural exponent: the bound of the sparsification lemma on the number of leaves is at most
2^(⌊n/2^s⌋+1) for the threshold τ = tauOf s, as soon as s ≥ s0K k. The estimate of the sum of
binomial coefficients is `WidthK.stLeafCount`. -/

@[expose] public section

namespace PaddedDescent.F.Arith


/-- The bound of the sparsification lemma for the number of leaves, for width k and s ≥ s0K k, is at
most 2^(⌊n/2^s⌋+1). -/
theorem sum_choose_le_two_pow {k s : ℕ} (hs : s0K k ≤ s) (n : ℕ) :
    ∑ j ∈ Finset.range (k * n / tauOf s + 1), (WidthK.bsum (tauOf s) k * n).choose j ≤ 2 ^ (n / 2 ^ s + 1) := by
  have h1 := WidthK.stLeafCount k (tauOf s) (1 / 2 ^ s) (le_trans (by norm_num) (two_le_tauOf s)) (tauOf_works hs) n
  have h2 : n < 2 ^ s * (n / 2 ^ s + 1) := Nat.lt_mul_div_succ n (by positivity)
  have h3 : (n : ℝ) ≤ (2 : ℝ) ^ s * ((n / 2 ^ s + 1 : ℕ) : ℝ) := by exact_mod_cast h2.le
  have h4 : (1 : ℝ) / 2 ^ s * (n : ℝ) ≤ ((n / 2 ^ s + 1 : ℕ) : ℝ) := by
    have hp : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
    rw [one_div, inv_mul_le_iff₀ hp]
    exact h3
  have h5 : ((∑ j ∈ Finset.range (k * n / tauOf s + 1), (WidthK.bsum (tauOf s) k * n).choose j : ℕ) : ℝ)
      ≤ ((2 ^ (n / 2 ^ s + 1) : ℕ) : ℝ) := by
    calc ((∑ j ∈ Finset.range (k * n / tauOf s + 1), (WidthK.bsum (tauOf s) k * n).choose j : ℕ) : ℝ)
        ≤ (2 : ℝ) ^ (1 / 2 ^ s * (n : ℝ)) := h1
      _ ≤ (2 : ℝ) ^ (((n / 2 ^ s + 1 : ℕ) : ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h4
      _ = ((2 ^ (n / 2 ^ s + 1) : ℕ) : ℝ) := by rw [Real.rpow_natCast]; push_cast; ring
  exact_mod_cast h5

end PaddedDescent.F.Arith
