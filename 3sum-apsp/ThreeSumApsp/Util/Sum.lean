/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Bounds on finite sums and products

General facts about sums and products over a finite set in an ordered ring or field.

* A sum of `s.card` numbers of absolute value at most `A` is at most `s.card * A` in absolute value
  (`Finset.abs_sum_le_card_mul`), also with coefficients of absolute value at most `1`
  (`Finset.abs_sum_mul_le`).
* A product of numbers of absolute value at most `1` has absolute value at most `1`
  (`Finset.abs_prod_le_one`). For integers, `Int.abs_le_one_iff` says that these are `0`, `1`, `-1`.
* A sum over the indices below `m * n` is a double sum (`Finset.sum_range_mul`).
* A part of a geometric series with ratio `0 < x < 1` is less than the whole series from its first
  term on (`geom_sum_Ico_lt_of_lt_one`).
-/

public section

namespace Finset

variable {ι R : Type*}

/-- If `|f i| ≤ A` for all `i ∈ s`, then `|∑ i ∈ s, f i| ≤ s.card * A`. -/
theorem abs_sum_le_card_mul [Ring R] [LinearOrder R] [IsOrderedRing R] (s : Finset ι) {f : ι → R}
    {A : R} (h : ∀ i ∈ s, |f i| ≤ A) : |∑ i ∈ s, f i| ≤ s.card * A :=
  (abs_sum_le_sum_abs f s).trans ((sum_le_card_nsmul s _ A h).trans_eq (nsmul_eq_mul _ _))

/-- If `|c i| ≤ 1` and `|a i| ≤ A` for all `i ∈ s`, then `|∑ i ∈ s, c i * a i| ≤ s.card * A`. -/
theorem abs_sum_mul_le [Ring R] [LinearOrder R] [IsOrderedRing R] (s : Finset ι) {c a : ι → R}
    {A : R} (hc : ∀ i ∈ s, |c i| ≤ 1) (ha : ∀ i ∈ s, |a i| ≤ A) :
    |∑ i ∈ s, c i * a i| ≤ s.card * A :=
  abs_sum_le_card_mul s fun i hi =>
    (abs_mul (c i) (a i)).trans_le
      ((mul_le_of_le_one_left (abs_nonneg _) (hc i hi)).trans (ha i hi))

/-- If `|f i| ≤ 1` for all `i ∈ s`, then `|∏ i ∈ s, f i| ≤ 1`. -/
theorem abs_prod_le_one [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] (s : Finset ι)
    {f : ι → R} (h : ∀ i ∈ s, |f i| ≤ 1) : |∏ i ∈ s, f i| ≤ 1 :=
  (abs_prod s f).trans_le (prod_le_one (fun _ _ => abs_nonneg _) h)

/-- A sum over the indices below `m * n`, row by row: the index `a * n + b` has row `a` and column
`b`. -/
theorem sum_range_mul {M : Type*} [AddCommMonoid M] (m n : ℕ) (F : ℕ → M) :
    ∑ i ∈ range (m * n), F i = ∑ a ∈ range m, ∑ b ∈ range n, F (a * n + b) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]

end Finset

/-- For `0 < x < 1`, `∑ i ∈ Ico m n, x ^ i < x ^ m / (1 - x)`. Mathlib's
`geom_sum_Ico_le_of_lt_one` has `≤`, for `0 ≤ x`. -/
theorem geom_sum_Ico_lt_of_lt_one {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {x : K} (hx : 0 < x) (hx1 : x < 1) (m n : ℕ) :
    ∑ i ∈ Finset.Ico m n, x ^ i < x ^ m / (1 - x) := by
  have hpos : 0 < 1 - x := sub_pos.2 hx1
  rcases le_total m n with hmn | hnm
  · rw [geom_sum_Ico' hx1.ne hmn]
    exact div_lt_div_of_pos_right (sub_lt_self _ (pow_pos hx n)) hpos
  · rw [Finset.Ico_eq_empty_of_le hnm, Finset.sum_empty]
    exact div_pos (pow_pos hx m) hpos
