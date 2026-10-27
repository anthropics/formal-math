/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.ParityChecks.RunDefs
public import ClauseBound.Rec.Few

/-! # Bounds on binomial coefficients, as used for the numbers of shared bits in Step 3 of Appendix D

A product of binomial coefficients is at most the binomial coefficient of the sums, because
C(a,i)·C(b,j) is one term of Vandermonde's formula for C(a+b, i+j). The logarithm of C(t, μ) is
at most μ'·max{1, log₂(3t/μ')} for μ ≤ μ': if μ' ≤ t, then C(t, μ) is one term of Σ_{ν ≤ μ'} C(t, ν)
≤ (3t/μ')^μ', and otherwise C(t, μ) ≤ 2^t ≤ 2^μ'. Rounding a logarithm up costs at most
one bit. -/

public section

namespace ClauseBound.ParityChecks

open Finset _root_.ParityChecks

namespace Binom

/-- C(a,i)·C(b,j) ≤ C(a+b, i+j). -/
theorem choose_mul_choose_le (a b i j : ℕ) : a.choose i * b.choose j ≤ (a + b).choose (i + j) := by
  rw [Nat.add_choose_eq]
  exact single_le_sum (f := fun ij : ℕ × ℕ => a.choose ij.1 * b.choose ij.2) (fun _ _ => Nat.zero_le _) (mem_antidiagonal.2 (rfl : (i, j).1 + (i, j).2 = i + j))

/-- Rounding a binary logarithm up costs at most one bit. -/
theorem clog_le_logb_add_one {x : ℕ} (hx : 1 ≤ x) : (Nat.clog 2 x : ℝ) ≤ Real.logb 2 x + 1 := by
  have h0 : 0 ≤ Real.logb 2 (x : ℝ) := Real.logb_nonneg (by norm_num) (by exact_mod_cast hx)
  have h1 := Real.natCeil_logb_natCast 2 x
  have h2 := Nat.ceil_lt_add_one h0
  rw [← h1]
  exact_mod_cast h2.le

end Binom

open Binom

/-- A product of binomial coefficients is at most the binomial coefficient of the sums. -/
theorem prod_choose_le {ι : Type} (s : Finset ι) (t μ : ι → ℕ) : ∏ i ∈ s, (t i).choose (μ i) ≤ (∑ i ∈ s, t i).choose (∑ i ∈ s, μ i) := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons a s ha ih =>
    rw [prod_cons, sum_cons, sum_cons]
    exact (Nat.mul_le_mul_left _ ih).trans (choose_mul_choose_le _ _ _ _)

/-- log₂ C(t, μ) ≤ μ'·max{1, log₂(3t/μ')} for μ ≤ μ', μ' ≥ 1. -/
theorem logb_choose_le {t μ μ' : ℕ} (h : μ ≤ μ') (h1 : 1 ≤ μ') :
    Real.logb 2 (t.choose μ) ≤ μ' * max 1 (Real.logb 2 (3 * t / μ')) := by
  have hμ0 : (0 : ℝ) ≤ μ' := Nat.cast_nonneg _
  rcases Nat.eq_zero_or_pos (t.choose μ) with h0 | h0
  · rw [h0, Nat.cast_zero, Real.logb_zero]
    exact mul_nonneg hμ0 (le_trans zero_le_one (le_max_left _ _))
  · have hpos : (0 : ℝ) < (t.choose μ : ℝ) := by exact_mod_cast h0
    rcases Nat.lt_or_ge t μ' with hlt | hge
    · have h2 : (t.choose μ : ℝ) ≤ 2 ^ μ' := by
        exact_mod_cast (Nat.choose_le_two_pow t μ).trans (Nat.pow_le_pow_right (by norm_num) hlt.le)
      calc Real.logb 2 (t.choose μ) ≤ Real.logb 2 ((2 : ℝ) ^ μ') := Real.logb_le_logb_of_le (by norm_num) hpos h2
        _ = μ' * 1 := by rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]
        _ ≤ μ' * max 1 (Real.logb 2 (3 * t / μ')) := mul_le_mul_of_nonneg_left (le_max_left _ _) hμ0
    · have h2 : (t.choose μ : ℝ) ≤ (3 * t / μ') ^ μ' := by
        refine le_trans ?_ (ClauseBound.Rec.sum_choose_le h1 hge)
        exact single_le_sum (f := fun ν => (t.choose ν : ℝ)) (fun _ _ => Nat.cast_nonneg _) (mem_range.2 (Nat.lt_succ_of_le h))
      calc Real.logb 2 (t.choose μ) ≤ Real.logb 2 ((3 * t / μ' : ℝ) ^ μ') := Real.logb_le_logb_of_le (by norm_num) hpos h2
        _ = μ' * Real.logb 2 (3 * t / μ') := by rw [Real.logb_pow]
        _ ≤ μ' * max 1 (Real.logb 2 (3 * t / μ')) := mul_le_mul_of_nonneg_left (le_max_right _ _) hμ0

end ClauseBound.ParityChecks
