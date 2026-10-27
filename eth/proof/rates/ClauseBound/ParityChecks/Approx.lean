/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ParityChecksStatement
public import Mathlib.Tactic

/-! # The truncated potential

Three fields of `ParityChecks.ChoiceByPotential`, as theorems of their own, on the term `Upar` of a
potential for the choice of checks (Step 2 of Appendix D; not the Υ printed there). In `Upar` the
power (1 − 2p)^u
is replaced by the first i₀ + 1 terms of its binomial series (`tUpar`). If that changes every power
with u ≤ |E| by at most ε, it changes `Upar` by at most ½·ε·|X|·C(|E|, nb + 1) (`approx`).
The truncated term is (5/8)^(r−1−j)·½·(A + Σ_{i ≤ i₀} (−2p)^i·B_i) with integers A and B_i
(`compute`), and |A| ≤ |X|·C(|E|, nb + 1), |B_i| ≤ |X|·C(|E|, nb + 1)·C(|E|, i) (`abs_le`). -/

public section

namespace ClauseBound.ParityChecks.Approx

open Finset _root_.ParityChecks

variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]

/-! ### Sizes of the factors -/

/-- [q even] is 0 or 1. -/
theorem ev_nonneg (q : ℕ) : 0 ≤ ev q := by
  unfold ev; split_ifs <;> norm_num

/-- [q even] is 0 or 1. -/
theorem ev_le_one (q : ℕ) : ev q ≤ 1 := by
  unfold ev; split_ifs <;> norm_num

/-- A product of numbers [q even] has absolute value at most 1. -/
theorem abs_prod_ev_le (s : Finset ℕ) (q : ℕ → ℕ) : |∏ i ∈ s, ev (q i)| ≤ 1 := by
  rw [abs_of_nonneg (Finset.prod_nonneg fun i _ => ev_nonneg _)]
  exact Finset.prod_le_one (fun i _ => ev_nonneg _) fun i _ => ev_le_one _

/-- The same for the rational numbers. -/
theorem abs_prod_ev_cast_le (s : Finset ℕ) (q : ℕ → ℕ) : |∏ i ∈ s, (ev (q i) : ℚ)| ≤ 1 := by
  have h := abs_prod_ev_le s q
  have h2 : ((|∏ i ∈ s, ev (q i)| : ℤ) : ℚ) ≤ ((1 : ℤ) : ℚ) := Int.cast_le.2 h
  simpa using h2

omit [Fintype X] [DecidableEq E] in
/-- ω(ξ) ≤ C(|E|, nb + 1). -/
theorem omega_le (V : X → Finset E) (nb : ℕ) (ξ : X) : omega V nb ξ ≤ (Fintype.card E).choose (nb + 1) :=
  Nat.choose_le_choose _ (Finset.card_le_univ _)

omit [DecidableEq E] in
/-- C(|s|, i) ≤ C(|E|, i) for every set s of elements of E. -/
theorem choose_card_le (s : Finset E) (i : ℕ) : (#s).choose i ≤ (Fintype.card E).choose i :=
  Nat.choose_le_choose _ (Finset.card_le_univ _)

/-! ### The three fields -/

/-- The error of the truncated series carries over to the potential. -/
theorem approx (V : X → Finset E) (nb r i₀ j : ℕ) (Λ : ℕ → Finset E) (D : Finset E) (ε : ℚ)
    (hε : ∀ u ≤ Fintype.card E, |(1 - 2 * pr nb) ^ u - ∑ i ∈ range (i₀ + 1), (-2 * pr nb) ^ i * (u.choose i : ℚ)| ≤ ε) :
    |tUpar V nb r i₀ j Λ D - Upar V nb r j Λ D| ≤ 1 / 2 * ε * (Fintype.card X * (Fintype.card E).choose (nb + 1) : ℕ) := by
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hε 0 (Nat.zero_le _))
  have hc0 : (0 : ℚ) ≤ (5 / 8) ^ (r - 1 - j) := by positivity
  have hc1 : (5 / 8 : ℚ) ^ (r - 1 - j) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hterm : ∀ ξ : X,
      |(omega V nb ξ : ℚ) * (∏ j' ∈ range j, (ev #(Λ j' ∩ V ξ) : ℚ)) *
          (1 / 2 * (1 + (-1) ^ #(Λ j ∩ V ξ) * ∑ i ∈ range (i₀ + 1), (-2 * pr nb) ^ i * ((#(D ∩ V ξ)).choose i : ℚ))) -
        (omega V nb ξ : ℚ) * (∏ j' ∈ range j, (ev #(Λ j' ∩ V ξ) : ℚ)) *
          (1 / 2 * (1 + (-1) ^ #(Λ j ∩ V ξ) * (1 - 2 * pr nb) ^ #(D ∩ V ξ)))| ≤
        ((Fintype.card E).choose (nb + 1) : ℚ) * 1 * (1 / 2 * (1 * ε)) := by
    intro ξ
    have h1 : |(omega V nb ξ : ℚ)| ≤ ((Fintype.card E).choose (nb + 1) : ℚ) := by
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      exact_mod_cast omega_le V nb ξ
    have h2 := abs_prod_ev_cast_le (range j) fun j' => #(Λ j' ∩ V ξ)
    have h3 : |(1 / 2 : ℚ)| ≤ 1 / 2 := by rw [abs_of_nonneg (by norm_num)]
    have h4 : |(-1 : ℚ) ^ #(Λ j ∩ V ξ)| ≤ 1 := by rw [abs_pow, abs_neg, abs_one, one_pow]
    have h5 : |∑ i ∈ range (i₀ + 1), (-2 * pr nb) ^ i * ((#(D ∩ V ξ)).choose i : ℚ) - (1 - 2 * pr nb) ^ #(D ∩ V ξ)| ≤ ε := by
      rw [abs_sub_comm]
      exact hε _ (Finset.card_le_univ _)
    rw [← mul_sub, ← mul_sub, add_sub_add_left_eq_sub, ← mul_sub, abs_mul, abs_mul, abs_mul, abs_mul]
    gcongr
  unfold tUpar Upar
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_nonneg hc0]
  calc (5 / 8 : ℚ) ^ (r - 1 - j) * |∑ ξ : X, _| ≤ 1 * ∑ _ξ : X, ((Fintype.card E).choose (nb + 1) : ℚ) * 1 * (1 / 2 * (1 * ε)) :=
        mul_le_mul hc1 ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ξ _ => hterm ξ)) (abs_nonneg _) zero_le_one
    _ = 1 / 2 * ε * (Fintype.card X * (Fintype.card E).choose (nb + 1) : ℕ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        push_cast
        ring

omit [Fintype E] in
/-- The truncated potential through the integers A and B_i. -/
theorem compute (V : X → Finset E) (nb r i₀ j : ℕ) (Λ : ℕ → Finset E) (D : Finset E) :
    tUpar V nb r i₀ j Λ D =
      (5 / 8) ^ (r - 1 - j) * (1 / 2) * ((Aint V nb j Λ : ℚ) + ∑ i ∈ range (i₀ + 1), (-2 * pr nb) ^ i * (Bint V nb i j Λ D : ℚ)) := by
  unfold tUpar Aint Bint
  push_cast
  rw [mul_assoc]
  congr 1
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [mul_add, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun i _ => by ring

/-- A and B_i are small. -/
theorem abs_le (V : X → Finset E) (nb i j : ℕ) (Λ : ℕ → Finset E) (D : Finset E) :
    |Aint V nb j Λ| ≤ (Fintype.card X * (Fintype.card E).choose (nb + 1) : ℕ) ∧
      |Bint V nb i j Λ D| ≤ (Fintype.card X * (Fintype.card E).choose (nb + 1) * (Fintype.card E).choose i : ℕ) := by
  have hw : ∀ ξ : X, |(omega V nb ξ : ℤ)| ≤ ((Fintype.card E).choose (nb + 1) : ℤ) := fun ξ => by
    rw [abs_of_nonneg (Int.natCast_nonneg _)]
    exact_mod_cast omega_le V nb ξ
  constructor
  · unfold Aint
    calc |∑ ξ : X, (omega V nb ξ : ℤ) * ∏ j' ∈ range j, ev #(Λ j' ∩ V ξ)|
        ≤ ∑ _ξ : X, ((Fintype.card E).choose (nb + 1) : ℤ) * 1 := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ξ _ => ?_)
          have h1 := hw ξ
          have h2 := abs_prod_ev_le (range j) fun j' => #(Λ j' ∩ V ξ)
          rw [abs_mul]
          gcongr
      _ = (Fintype.card X * (Fintype.card E).choose (nb + 1) : ℕ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          push_cast
          ring
  · unfold Bint
    calc |∑ ξ : X, (omega V nb ξ : ℤ) * ((#(D ∩ V ξ)).choose i : ℤ) * (-1) ^ #(Λ j ∩ V ξ) * ∏ j' ∈ range j, ev #(Λ j' ∩ V ξ)|
        ≤ ∑ _ξ : X, ((Fintype.card E).choose (nb + 1) : ℤ) * ((Fintype.card E).choose i : ℤ) * 1 * 1 := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ξ _ => ?_)
          have h1 := hw ξ
          have h2 := abs_prod_ev_le (range j) fun j' => #(Λ j' ∩ V ξ)
          have h3 : |((#(D ∩ V ξ)).choose i : ℤ)| ≤ ((Fintype.card E).choose i : ℤ) := by
            rw [abs_of_nonneg (Int.natCast_nonneg _)]
            exact_mod_cast choose_card_le (D ∩ V ξ) i
          have h4 : |(-1 : ℤ) ^ #(Λ j ∩ V ξ)| ≤ 1 := by rw [abs_pow, abs_neg, abs_one, one_pow]
          rw [abs_mul, abs_mul, abs_mul]
          gcongr
      _ = (Fintype.card X * (Fintype.card E).choose (nb + 1) * (Fintype.card E).choose i : ℕ) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          push_cast
          ring

end ClauseBound.ParityChecks.Approx
