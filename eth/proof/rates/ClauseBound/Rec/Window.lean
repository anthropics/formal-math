/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Computability.TuringMachine.Computable
public import Mathlib.Data.Int.Star
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.Tactic
public import PiecesStatement

/-! # Signs and binomial coefficients

Two lemmas: for a natural number j, the sign written with a case distinction on the parity of j is
(−1)^j; and for an integer a of any sign, the binomial coefficient C(a, k) = a(a − 1)⋯(a − k + 1)/k!
(`Ring.choose`) satisfies |C(a, k)| ≤ 2^(|a| + k). -/

@[expose] public section

namespace ClauseBound.Rec

open Finset

/-- The sign written with a case distinction is the power of −1. -/
theorem ite_even_natCast (j : ℕ) : (if Even (j : ℤ) then (1 : ℤ) else -1) = (-1) ^ j := by
  by_cases h : Even j
  · rw [if_pos (by exact_mod_cast h), h.neg_one_pow]
  · rw [if_neg (by exact_mod_cast h), (Nat.not_even_iff_odd.1 h).neg_one_pow]

/-- |C(a, k)| ≤ 2^(|a| + k). -/
theorem abs_choose_le (a : ℤ) (k : ℕ) : |Ring.choose a k| ≤ 2 ^ (a.natAbs + k) := by
  rcases le_or_gt 0 a with h | h
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [Ring.choose_natCast, Int.natAbs_natCast, abs_of_nonneg (by positivity)]
    calc ((n.choose k : ℕ) : ℤ) ≤ ((2 ^ n : ℕ) : ℤ) := by exact_mod_cast Nat.choose_le_two_pow n k
      _ ≤ 2 ^ (n + k) := by push_cast; exact pow_le_pow_right₀ (by norm_num) (by omega)
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (a := -a - 1) (by omega)
    obtain rfl : a = -((n : ℤ) + 1) := by omega
    rw [Ring.choose_neg, show (n : ℤ) + 1 + k - 1 = ((n + k : ℕ) : ℤ) by push_cast; ring, Ring.choose_natCast, Units.smul_def, smul_eq_mul, abs_mul,
      Int.abs_negOnePow, one_mul, abs_of_nonneg (by positivity), show (-((n : ℤ) + 1)).natAbs = n + 1 by omega]
    calc (((n + k).choose k : ℕ) : ℤ) ≤ ((2 ^ (n + k) : ℕ) : ℤ) := by exact_mod_cast Nat.choose_le_two_pow (n + k) k
      _ ≤ 2 ^ (n + 1 + k) := by push_cast; exact pow_le_pow_right₀ (by norm_num) (by omega)

end ClauseBound.Rec
