/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ParityChecksStatement
public import Mathlib.Analysis.SpecialFunctions.Exp

/-! # The potential: its sign, its value at the start, and the passage from one check to the next

The checks are chosen one clause at a time so that a potential Υ = Υ_par + Υ_inc + Υ_row + Υ_col
(`ParityChecks.Ups`) does not grow. Here, for p = 1/nb with nb ≥ 2:

* all four terms are nonnegative (`nonneg`);
* ½(1 + (1 − 2p)^v) < 5/8 for v > nb (`five_eighths`), because (1 − 2p)^v ≤ exp(−2v/nb) < exp(−2) ≤
  1/4;
* before the first decision the last three terms are 1/8 each and Υ_par ≤ (5/8)^r·Σ_ξ ω(ξ), where
  ω(ξ) = C(|V(ξ)|, nb + 1) (`omega`), so Υ ≤ 1/2 if (5/8)^r·|X|·C(|E|, nb + 1) ≤ 1/8 (`start`);
* the state in which all clauses are decided for check j, seen as the state in which check j + 1
  begins, has the same last three terms and a Υ_par that is not larger (`boundary`).

These are four of the fields of `ParityChecks.ChoiceByPotential`. -/

public section

namespace ClauseBound.ParityChecks.Start

open _root_.ParityChecks Finset

/-! ### The number p and the two factors -/

/-- p > 0. -/
theorem pr_pos {nb : ℕ} (h : 2 ≤ nb) : 0 < pr nb := by
  have : (0 : ℚ) < nb := by exact_mod_cast (by omega : 0 < nb)
  unfold pr; positivity

/-- 0 ≤ 1 − 2p. -/
theorem one_sub_nonneg {nb : ℕ} (h : 2 ≤ nb) : 0 ≤ 1 - 2 * pr nb := by
  have h2 : (2 : ℚ) ≤ nb := by exact_mod_cast h
  have : pr nb ≤ 1 / 2 := by unfold pr; exact one_div_le_one_div_of_le (by norm_num) h2
  linarith

/-- 1 − 2p ≤ 1. -/
theorem one_sub_le_one {nb : ℕ} (h : 2 ≤ nb) : 1 - 2 * pr nb ≤ 1 := by
  have := pr_pos h
  linarith

/-- ½(1 + (−1)^q) = [q even]. -/
theorem half_ev (q : ℕ) : (1 / 2 : ℚ) * (1 + (-1) ^ q) = (ev q : ℚ) := by
  unfold ev
  rcases Nat.even_or_odd q with h | h
  · rw [h.neg_one_pow, if_pos h]; norm_num
  · rw [h.neg_one_pow, if_neg (Nat.not_even_iff_odd.2 h)]; norm_num

/-- [q even] ≥ 0. -/
theorem ev_nonneg (q : ℕ) : (0 : ℚ) ≤ (ev q : ℚ) := by
  unfold ev; split_ifs <;> simp

/-- ½(1 ± t^u) ≥ 0 for 0 ≤ t ≤ 1. -/
theorem factor_nonneg {t : ℚ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (a u : ℕ) : 0 ≤ 1 / 2 * (1 + (-1) ^ a * t ^ u) := by
  have h2 : t ^ u ≤ 1 := pow_le_one₀ h0 h1
  have h3 : 0 ≤ t ^ u := pow_nonneg h0 u
  rcases neg_one_pow_eq_or ℚ a with h | h <;> rw [h] <;> linarith

/-- (1 − 2/nb)^v < 1/4 for v > nb ≥ 2, in the real numbers. -/
theorem pow_lt_quarter (nb v : ℕ) (hnb : 2 ≤ nb) (hv : nb < v) : ((1 : ℝ) - 2 / nb) ^ v < 1 / 4 := by
  have hn : (0 : ℝ) < nb := by exact_mod_cast (by omega : 0 < nb)
  have hn2 : (2 : ℝ) ≤ nb := by exact_mod_cast hnb
  have h0 : 0 ≤ (1 : ℝ) - 2 / nb := by rw [sub_nonneg, div_le_one hn]; exact hn2
  have h1 : (1 : ℝ) - 2 / nb ≤ Real.exp (-(2 / nb)) := Real.one_sub_le_exp_neg _
  have h2 : ((1 : ℝ) - 2 / nb) ^ v ≤ Real.exp (-(2 / nb)) ^ v := pow_le_pow_left₀ h0 h1 v
  have h3 : Real.exp (-(2 / nb)) ^ v = Real.exp (v * (-(2 / nb))) := (Real.exp_nat_mul _ _).symm
  have h4 : (v : ℝ) * (-(2 / nb)) < -2 := by
    have hv' : (nb : ℝ) < v := by exact_mod_cast hv
    have h5 : 1 < (v : ℝ) / nb := by rwa [one_lt_div hn]
    have e : (v : ℝ) * (-(2 / nb)) = -2 * (v / nb) := by ring
    rw [e]; linarith
  have h5 : Real.exp (v * (-(2 / nb))) < Real.exp (-2) := Real.exp_lt_exp.2 h4
  have h6 : Real.exp (-2) ≤ 1 / 4 := by
    have e1 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    have e3 : 4 ≤ Real.exp 2 := by rw [e2]; nlinarith
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) e3
  rw [h3] at h2
  linarith

/-- ½(1 + (1 − 2p)^v) < 5/8 for v > nb. -/
theorem five_eighths : ∀ nb v : ℕ, 2 ≤ nb → nb < v → 1 / 2 * (1 + (1 - 2 * pr nb) ^ v) < 5 / 8 := by
  intro nb v hnb hv
  have key : ((1 : ℚ) - 2 * pr nb) ^ v < 1 / 4 := by
    have h : ((((1 : ℚ) - 2 * (1 / nb)) ^ v : ℚ) : ℝ) < ((1 / 4 : ℚ) : ℝ) := by
      have := pow_lt_quarter nb v hnb hv
      push_cast
      have e : (1 : ℝ) - 2 * (1 / nb) = 1 - 2 / nb := by ring
      rw [e]; exact this
    unfold pr
    exact_mod_cast h
  linarith

/-- The term of one ξ with v violated clauses when a check begins: the factor ½(1 + (1 − 2p)^v) may
be replaced by 5/8. -/
theorem term_le (nb v : ℕ) (hnb : 2 ≤ nb) (c : ℚ) (hc : 0 ≤ c) :
    ((v.choose (nb + 1) : ℕ) : ℚ) * c * (1 / 2 * (1 + (1 - 2 * pr nb) ^ v)) ≤ ((v.choose (nb + 1) : ℕ) : ℚ) * c * (5 / 8) := by
  rcases Nat.lt_or_ge nb v with h | h
  · have := (five_eighths nb v hnb h).le
    gcongr
  · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp

section
variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]

omit [DecidableEq E] in
/-- Σ_ξ ω(ξ) ≤ |X|·C(|E|, nb + 1). -/
theorem sum_omega_le (V : X → Finset E) (nb : ℕ) :
    (∑ ξ, (omega V nb ξ : ℚ)) ≤ ((Fintype.card X * (Fintype.card E).choose (nb + 1) : ℕ) : ℚ) := by
  have h : ∑ ξ, omega V nb ξ ≤ Fintype.card X * (Fintype.card E).choose (nb + 1) := by
    have := Finset.sum_le_card_nsmul (univ : Finset X) (omega V nb) ((Fintype.card E).choose (nb + 1))
      (fun ξ _ => Nat.choose_le_choose _ (Finset.card_le_univ _))
    simpa [Finset.card_univ] using this
  exact_mod_cast h

/-- Υ_par when check j begins. -/
theorem Upar_fresh_le (V : X → Finset E) (nb r j : ℕ) (Λ : ℕ → Finset E) (hnb : 2 ≤ nb) (hΛ : Λ j = ∅) :
    Upar V nb r j Λ univ ≤
      (5 / 8) ^ (r - 1 - j) * (5 / 8 * ∑ ξ, (omega V nb ξ : ℚ) * ∏ j' ∈ range j, (ev #(Λ j' ∩ V ξ) : ℚ)) := by
  unfold Upar
  rw [Finset.mul_sum (a := (5 / 8 : ℚ))]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ξ _ => ?_) (by positivity)
  rw [hΛ]
  simp only [empty_inter, card_empty, pow_zero, one_mul, univ_inter]
  have := term_le nb #(V ξ) hnb (∏ j' ∈ range j, (ev #(Λ j' ∩ V ξ) : ℚ)) (Finset.prod_nonneg fun _ _ => ev_nonneg _)
  unfold omega
  linarith

omit [Fintype E] in
/-- Υ_par when all clauses are decided for check j. -/
theorem Upar_done (V : X → Finset E) (nb r j : ℕ) (Λ : ℕ → Finset E) :
    Upar V nb r j Λ ∅ = (5 / 8) ^ (r - 1 - j) * ∑ ξ, (omega V nb ξ : ℚ) * ∏ j' ∈ range (j + 1), (ev #(Λ j' ∩ V ξ) : ℚ) := by
  unfold Upar
  congr 1
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [Finset.prod_range_succ, ← half_ev #(Λ j ∩ V ξ)]
  simp only [empty_inter, card_empty, pow_zero, mul_one]
  ring

omit [DecidableEq E] in
/-- The clauses not yet decided, check by check: the same before and after the passage to the next
check. -/
theorem undRow_next (j : ℕ) : undRow (j + 1) (univ : Finset E) = undRow j (∅ : Finset E) := by
  funext j'
  unfold undRow
  simp only [card_univ, card_empty]
  split_ifs <;> first | rfl | omega

/-- The checks not yet decided, clause by clause: the same before and after the passage to the next
check. -/
theorem undCol_next (r j : ℕ) (h : j + 1 < r) : undCol r (j + 1) (univ : Finset E) = undCol r j (∅ : Finset E) := by
  funext e
  unfold undCol
  simp only [mem_univ, if_true, notMem_empty, if_false]
  omega

end

/-! ### The four statements -/

/-- All four terms of the potential are nonnegative. -/
theorem nonneg : ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb r j : ℕ) (Λ : ℕ → Finset E) (D : Finset E), 2 ≤ nb →
    0 ≤ Upar V nb r j Λ D ∧ 0 ≤ Uinc nb r j Λ D ∧ 0 ≤ Urow nb r j Λ D ∧ 0 ≤ Ucol nb r j Λ D := by
  intro X E _ _ _ V nb r j Λ D hnb
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold Upar
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun ξ _ => ?_)
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg fun _ _ => ev_nonneg _))
      (factor_nonneg (one_sub_nonneg hnb) (one_sub_le_one hnb) _ _)
  · unfold Uinc pr; positivity
  · unfold Urow pr
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)
  · unfold Ucol pr
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity)

/-- At the start the potential is at most 1/2. -/
theorem start : ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb r : ℕ), 2 ≤ nb → 1 ≤ r → 1 ≤ Fintype.card E →
    (5 / 8 : ℚ) ^ r * (Fintype.card X * (Fintype.card E).choose (nb + 1) : ℕ) ≤ 1 / 8 → Ups V nb r 0 (fun _ => ∅) univ ≤ 1 / 2 := by
  intro X E _ _ _ V nb r hnb hr hm hsmall
  have hp := pr_pos hnb
  have hr' : (0 : ℚ) < r := by exact_mod_cast hr
  have hm' : (0 : ℚ) < Fintype.card E := by exact_mod_cast hm
  have h1 : Upar V nb r 0 (fun _ => ∅) univ ≤ 1 / 8 := by
    refine (Upar_fresh_le V nb r 0 (fun _ => ∅) hnb rfl).trans (le_trans ?_ hsmall)
    have e : (5 / 8 : ℚ) ^ r = (5 / 8) ^ (r - 1 - 0) * (5 / 8) := by
      rw [← pow_succ]; congr 1; omega
    rw [e, mul_assoc]
    simp only [range_zero, prod_empty, mul_one]
    have := sum_omega_le V nb
    gcongr
  have h2 : Uinc nb r 0 (fun _ => (∅ : Finset E)) univ = 1 / 8 := by
    unfold Uinc undRow
    simp only [card_empty, sum_const_zero, Nat.not_lt_zero, if_false, card_univ, ite_self, sum_const, card_range, smul_eq_mul]
    push_cast
    field_simp
    ring
  have h3 : Urow nb r 0 (fun _ => (∅ : Finset E)) univ = 1 / 8 := by
    unfold Urow undRow
    simp only [card_empty, Nat.not_lt_zero, if_false, card_univ, ite_self, Nat.sub_self, pow_zero, div_one, sum_const, card_range, nsmul_eq_mul, mul_one]
    field_simp
  have h4 : Ucol nb r 0 (fun _ => (∅ : Finset E)) univ = 1 / 8 := by
    have e : ∀ x : E, r - undCol r 0 univ x = 0 := by
      intro x; unfold undCol; simp only [mem_univ, if_true]; omega
    unfold Ucol
    simp only [e, notMem_empty, filter_false, card_empty, pow_zero, div_one, sum_const, card_univ, nsmul_eq_mul, mul_one]
    field_simp
  unfold Ups
  rw [h2, h3, h4]
  linarith

/-- From one check to the next the potential does not grow. -/
theorem boundary : ∀ (X E : Type) [Fintype X] [Fintype E] [DecidableEq E] (V : X → Finset E) (nb r j : ℕ) (Λ : ℕ → Finset E),
    2 ≤ nb → IsState r j Λ ∅ → j + 1 < r → Ups V nb r (j + 1) Λ univ ≤ Ups V nb r j Λ ∅ := by
  intro X E _ _ _ V nb r j Λ hnb hst hj
  have h1 : Upar V nb r (j + 1) Λ univ ≤ Upar V nb r j Λ ∅ := by
    refine (Upar_fresh_le V nb r (j + 1) Λ hnb (hst.later _ (Nat.lt_succ_self j))).trans (le_of_eq ?_)
    rw [Upar_done, ← mul_assoc, ← pow_succ]
    congr 2
    omega
  have h2 : Uinc nb r (j + 1) Λ (univ : Finset E) = Uinc nb r j Λ ∅ := by
    unfold Uinc; rw [undRow_next]
  have h3 : Urow nb r (j + 1) Λ (univ : Finset E) = Urow nb r j Λ ∅ := by
    unfold Urow; rw [undRow_next]
  have h4 : Ucol nb r (j + 1) Λ (univ : Finset E) = Ucol nb r j Λ ∅ := by
    unfold Ucol; rw [undCol_next r j hj]
  unfold Ups
  rw [h2, h3, h4]
  linarith

end ClauseBound.ParityChecks.Start
