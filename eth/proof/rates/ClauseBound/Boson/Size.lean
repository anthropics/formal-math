/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClauseBound.Boson.Defs2
public import ClauseBound.Boson.Basic
public import ClauseBound.Rec.Window

/-! # Sizes of the entries of the matrices

The entry of the matrix of a[r] at monomials t^π, t^σ of weight at most W (the coefficient of t^π in
a[r] t^σ), for a monomial a with parts at most W, is at most 2^{(4W+1)·(number of parts of a)} in
absolute value
(`abs_op_le`). The proof is an induction on the list of the parts. One step of the recursion is a
sum over the different parts l of π, of which there are at most W + 1, and a sum
over the different parts k of σ with the factors k·(number of parts equal to k), which add up to the
weight of σ. All binomial coefficients that occur are at most 2^{2W}. So one
step multiplies the bound by at most (2W + 1)·2^{2W} ≤ 2^{4W+1}. -/

public section

namespace ClauseBound.Boson

open Finset

namespace Size

/-- |C(r − 1, n − 1)| ≤ 2^{2W} for n ≤ W and |r| ≤ W. -/
theorem abs_bet_le {W n : ℕ} (hW : 1 ≤ W) (hn : n ≤ W) {r : ℤ} (h1 : -(W : ℤ) ≤ r) (h2 : r ≤ W) : |bet n r| ≤ 2 ^ (2 * W) := by
  unfold bet
  split_ifs
  · rw [abs_zero]; positivity
  · exact (ClauseBound.Rec.abs_choose_le (r - 1) (n - 1)).trans (pow_le_pow_right₀ (by norm_num) (by omega))

/-- A part of a monomial is at most its weight. -/
theorem le_sum_of_mem {π : Multiset ℕ} {l : ℕ} (h : l ∈ π) : l ≤ π.sum := by
  rw [← Multiset.sum_erase h]
  exact Nat.le_add_right _ _

/-- Taking a part away does not raise the weight. -/
theorem sum_erase_le (π : Multiset ℕ) (l : ℕ) : (π.erase l).sum ≤ π.sum := by
  by_cases h : l ∈ π
  · rw [← Multiset.sum_erase h]
    exact Nat.le_add_left _ _
  · rw [Multiset.erase_of_notMem h]

/-- A monomial of weight at most W has at most W + 1 different parts. -/
theorem card_toFinset_le {π : Multiset ℕ} {W : ℕ} (h : π.sum ≤ W) : #π.toFinset ≤ W + 1 := by
  rw [← card_range (W + 1)]
  exact card_le_card fun l hl => mem_range.2 (Nat.lt_succ_of_le ((le_sum_of_mem (Multiset.mem_toFinset.1 hl)).trans h))

/-- The weight of a monomial is the sum of k·(number of parts equal to k). -/
theorem sum_mul_count (σ : Multiset ℕ) : ∑ k ∈ σ.toFinset, (k : ℤ) * (σ.count k : ℤ) = (σ.sum : ℤ) := by
  conv_rhs => rw [Finset.sum_multiset_count σ]
  push_cast
  exact sum_congr rfl fun k _ => by rw [smul_eq_mul, Nat.cast_mul, mul_comm]

/-- One step of the recursion multiplies a bound B for the entries by at most 2^{4W+1}. -/
theorem abs_nop_le {W n : ℕ} (hW : 1 ≤ W) (hn : n ≤ W) {F : ℤ → Ker} {B : ℤ} (hB : 0 ≤ B)
    (hF : ∀ (r : ℤ) (π σ : Multiset ℕ), π.sum ≤ W → σ.sum ≤ W → |F r π σ| ≤ B) (r : ℤ) {π σ : Multiset ℕ} (hπ : π.sum ≤ W) (hσ : σ.sum ≤ W) :
    |nop n F r π σ| ≤ 2 ^ (4 * W + 1) * B := by
  have hp : (0 : ℤ) ≤ 2 ^ (2 * W) := by positivity
  have h1 : |∑ l ∈ π.toFinset, bet n l * cre l (F (r - l)) π σ| ≤ ((W : ℤ) + 1) * (2 ^ (2 * W) * B) := by
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_card_nsmul _ _ (2 ^ (2 * W) * B) fun l hl => ?_).trans ?_)
    · have hl' := Multiset.mem_toFinset.1 hl
      have hlW : l ≤ W := (le_sum_of_mem hl').trans hπ
      rw [abs_mul, cre, if_pos hl']
      exact mul_le_mul (abs_bet_le hW hn (by omega) (by exact_mod_cast hlW)) (hF _ _ _ ((sum_erase_le π l).trans hπ) hσ) (abs_nonneg _) hp
    · rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_toFinset_le hπ) (mul_nonneg hp hB)
  have h2 : |∑ k ∈ σ.toFinset, bet n (-(k : ℤ)) * ann (F (r + k)) k π σ| ≤ (W : ℤ) * (2 ^ (2 * W) * B) := by
    calc |∑ k ∈ σ.toFinset, bet n (-(k : ℤ)) * ann (F (r + k)) k π σ|
        ≤ ∑ k ∈ σ.toFinset, ((k : ℤ) * (σ.count k : ℤ)) * (2 ^ (2 * W) * B) := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k hk => ?_)
          have hkW : k ≤ W := (le_sum_of_mem (Multiset.mem_toFinset.1 hk)).trans hσ
          have hc : (0 : ℤ) ≤ (k : ℤ) * (σ.count k : ℤ) := by positivity
          rw [abs_mul, ann, abs_mul, abs_of_nonneg hc, mul_left_comm]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul (abs_bet_le hW hn (by omega) (by omega)) (hF _ _ _ hπ ((sum_erase_le σ k).trans hσ)) (abs_nonneg _) hp) hc
      _ = (σ.sum : ℤ) * (2 ^ (2 * W) * B) := by rw [← sum_mul, sum_mul_count]
      _ ≤ (W : ℤ) * (2 ^ (2 * W) * B) := mul_le_mul_of_nonneg_right (by exact_mod_cast hσ) (mul_nonneg hp hB)
  have h3 : (2 * (W : ℤ) + 1) ≤ 2 ^ (2 * W + 1) := by exact_mod_cast (Nat.lt_two_pow_self (n := 2 * W + 1)).le
  calc |nop n F r π σ| ≤ ((W : ℤ) + 1) * (2 ^ (2 * W) * B) + (W : ℤ) * (2 ^ (2 * W) * B) := (abs_add_le _ _).trans (add_le_add h1 h2)
    _ = (2 * (W : ℤ) + 1) * (2 ^ (2 * W) * B) := by ring
    _ ≤ 2 ^ (2 * W + 1) * (2 ^ (2 * W) * B) := mul_le_mul_of_nonneg_right h3 (mul_nonneg hp hB)
    _ = 2 ^ (4 * W + 1) * B := by rw [← mul_assoc, ← pow_add]; congr 2; ring

end Size

/-- If all weights and parts are at most W, an entry of the matrix of a[r] is at most
2^{(4W+1)·(number of parts of a)} in absolute value. -/
theorem abs_op_le {W : ℕ} (hW : 1 ≤ W) (a : List ℕ) (ha : ∀ n ∈ a, n ≤ W) (r : ℤ) {π σ : Multiset ℕ} (hπ : π.sum ≤ W) (hσ : σ.sum ≤ W) :
    |op a r π σ| ≤ 2 ^ ((4 * W + 1) * a.length) := by
  induction a generalizing r π σ with
  | nil =>
    rw [List.length_nil, Nat.mul_zero, pow_zero, op]
    split_ifs
    · unfold one
      split_ifs <;> simp
    · simp
  | cons n a ih =>
    rw [List.length_cons, Nat.mul_succ, Nat.add_comm, pow_add, op]
    exact Size.abs_nop_le hW (ha n List.mem_cons_self) (by positivity)
      (fun r π σ hπ hσ => ih (fun m hm => ha m (List.mem_cons_of_mem _ hm)) r hπ hσ) r hπ hσ

end ClauseBound.Boson
