/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ParityChecksStatement
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Parity checks: the first step

Lemmas for Step 1 of Appendix D of the paper (parity checks, and a cut-off modulo a power of 2):

* the two expansions [q even] = Σ_i σ_i·C(q,i) and (−1)^q = Σ_i (−2)^i·C(q,i);
* if the checks are good, the inclusion–exclusion sum cut off at nb marks, times the indicators that
  every check is violated an even number of times, is the indicator that no clause is
  violated;
* the cut-off lemma (Lemma 12) for one ξ: modulo 2^ν only the tuples of marks with at most M marks
  count, if M ≥ ν − 1 + |J₁|.

For the cut-off lemma: without the bound on the number of marks the two sides are equal, because a
product of sums over subsets is a sum over tuples of subsets; and the term of a tuple with
more than M marks is divisible by 2^ν, because σ_i is divisible by 2^(i−1) and (−2)^i by 2^i. -/

public section

namespace ClauseBound.ParityChecks.StepOne

open Finset _root_.ParityChecks

/-! ### The expansions -/

/-- 2σ_i = (−2)^i + [i = 0]. -/
theorem two_mul_sig (i : ℕ) : 2 * sig i = (-2) ^ i + if i = 0 then 1 else 0 := by
  unfold sig
  cases i with
  | zero => simp
  | succ k =>
    rw [if_neg (Nat.succ_ne_zero k), if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel, show (-2 : ℤ) = -1 * 2 by norm_num, mul_pow, pow_succ (2 : ℤ) k]
    ring

/-- 2·[q even] = 1 + (−1)^q. -/
theorem two_mul_ev (q : ℕ) : 2 * ev q = 1 + (-1) ^ q := by
  unfold ev
  by_cases h : Even q
  · rw [if_pos h, h.neg_one_pow]; norm_num
  · rw [if_neg h, (Nat.not_even_iff_odd.1 h).neg_one_pow]; norm_num

/-- (−1)^q = Σ_i (−2)^i·C(q,i). -/
theorem neg_one_pow_eq (q : ℕ) : (-1 : ℤ) ^ q = ∑ i ∈ range (q + 1), (-2 : ℤ) ^ i * q.choose i := by
  have h := add_pow (-2 : ℤ) 1 q
  rw [show (-2 : ℤ) + 1 = -1 by norm_num] at h
  rw [h]
  exact sum_congr rfl fun i _ => by rw [one_pow, mul_one]

/-- [q even] = Σ_i σ_i·C(q,i). -/
theorem ev_eq (q : ℕ) : ev q = ∑ i ∈ range (q + 1), sig i * q.choose i := by
  have h1 : ∑ i ∈ range (q + 1), (if i = 0 then (1 : ℤ) else 0) * q.choose i = 1 := by
    rw [sum_eq_single 0 (fun i _ hi => by rw [if_neg hi, zero_mul]) (fun h => absurd (mem_range.2 (Nat.succ_pos q)) h)]
    simp
  have h2 : 2 * ∑ i ∈ range (q + 1), sig i * q.choose i = 2 * ev q := by
    rw [two_mul_ev, neg_one_pow_eq, ← h1, ← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, two_mul_sig]
    ring
  linarith

/-- The sum of σ over the subsets of a set, by their numbers of elements. -/
theorem sum_powerset_sig {E : Type} (A : Finset E) : ∑ s ∈ A.powerset, sig #s = ev #A := by
  rw [sum_powerset_apply_card, ev_eq]
  exact sum_congr rfl fun i _ => by rw [nsmul_eq_mul, mul_comm]

/-- The sum of (−2)^|s| over the subsets s of a set. -/
theorem sum_powerset_neg_two {E : Type} (A : Finset E) : ∑ s ∈ A.powerset, (-2 : ℤ) ^ #s = (-1) ^ #A := by
  rw [sum_powerset_apply_card (fun i => (-2 : ℤ) ^ i), neg_one_pow_eq]
  exact sum_congr rfl fun i _ => by rw [nsmul_eq_mul, mul_comm]

/-- The sum of (−1)^|s| over the subsets s of a set that is not empty. -/
theorem sum_powerset_neg_one' {E : Type} [DecidableEq E] {A : Finset E} (hA : A ≠ ∅) : ∑ s ∈ A.powerset, (-1 : ℤ) ^ #s = 0 := by
  rw [sum_powerset_neg_one_pow_card, if_neg hA]

/-! ### The product identity -/

theorem product {X E : Type} [DecidableEq E] (V : X → Finset E) (nb r : ℕ) (Λ : ℕ → Finset E) (hG : ∀ ξ, nb < #(V ξ) → ∃ j < r, Odd #(Λ j ∩ V ξ))
    (ξ : X) : (∑ S ∈ (V ξ).powerset with #S ≤ nb, (-1 : ℤ) ^ #S) * ∏ j ∈ range r, ev #(Λ j ∩ V ξ) = if V ξ = ∅ then 1 else 0 := by
  by_cases h0 : V ξ = ∅
  · rw [if_pos h0, h0, powerset_empty, filter_true_of_mem (fun S hS => by rw [mem_singleton.1 hS, card_empty]; exact Nat.zero_le _),
      sum_singleton, card_empty, pow_zero, one_mul]
    exact prod_eq_one fun j _ => by rw [inter_empty, card_empty]; rfl
  · rw [if_neg h0]
    rcases Nat.lt_or_ge nb #(V ξ) with h | h
    · obtain ⟨j, hj, hodd⟩ := hG ξ h
      rw [prod_eq_zero (mem_range.2 hj) (by rw [ev, if_neg (Nat.not_even_iff_odd.2 hodd)]), mul_zero]
    · rw [filter_true_of_mem fun S hS => (card_le_card (mem_powerset.1 hS)).trans h, sum_powerset_neg_one' h0, zero_mul]

/-! ### The cut-off lemma -/

section Cutoff

variable {E : Type} {r : ℕ}

/-- The factor of check j in the term of a tuple. -/
def fac (J₁ J₂ : Finset (Fin r)) (j : Fin r) (s : Finset E) : ℤ := if j ∈ J₁ then sig #s else if j ∈ J₂ then (-2) ^ #s else 1

/-- Two products over disjoint sets of checks as one product over all checks. -/
theorem prod_mul_prod {J₁ J₂ : Finset (Fin r)} (hJ : Disjoint J₁ J₂) (a b : Fin r → ℤ) :
    (∏ j ∈ J₁, a j) * ∏ j ∈ J₂, b j = ∏ j, if j ∈ J₁ then a j else if j ∈ J₂ then b j else 1 := by
  have h : ∀ j : Fin r, (if j ∈ J₁ then a j else if j ∈ J₂ then b j else 1) = (if j ∈ J₁ then a j else 1) * if j ∈ J₂ then b j else 1 := by
    intro j
    by_cases h1 : j ∈ J₁
    · rw [if_pos h1, if_pos h1, if_neg (disjoint_left.1 hJ h1), mul_one]
    · rw [if_neg h1, if_neg h1, one_mul]
  simp only [h]
  rw [prod_mul_distrib, prod_ite_mem, prod_ite_mem, univ_inter, univ_inter]

/-- The sets from which the members of a tuple are taken. -/
def dom (A : Fin r → Finset E) (J : Finset (Fin r)) (j : Fin r) : Finset (Finset E) := if j ∈ J then (A j).powerset else {∅}

/-- Without a bound on the number of marks: the sum over all tuples is the product. -/
theorem sum_all {J₁ J₂ : Finset (Fin r)} (hJ : Disjoint J₁ J₂) (A : Fin r → Finset E) :
    ∑ S ∈ Fintype.piFinset (dom A (J₁ ∪ J₂)), ∏ j, fac J₁ J₂ j (S j) = (∏ j ∈ J₁, ev #(A j)) * ∏ j ∈ J₂, (-1 : ℤ) ^ #(A j) := by
  rw [← prod_univ_sum, prod_mul_prod hJ]
  refine prod_congr rfl fun j _ => ?_
  unfold dom fac
  by_cases h1 : j ∈ J₁
  · simp only [if_pos h1, if_pos (mem_union_left J₂ h1)]
    exact sum_powerset_sig _
  · by_cases h2 : j ∈ J₂
    · simp only [if_neg h1, if_pos h2, if_pos (mem_union_right J₁ h2)]
      exact sum_powerset_neg_two _
    · have h3 : j ∉ J₁ ∪ J₂ := fun h => (mem_union.1 h).elim h1 h2
      simp only [if_neg h1, if_neg h2, if_neg h3, sum_singleton]

/-- σ_i is divisible by 2^(i−1). -/
theorem two_pow_dvd_sig (i : ℕ) : (2 : ℤ) ^ (i - 1) ∣ sig i := by
  unfold sig
  split_ifs with h
  · rw [h]; exact one_dvd _
  · exact Dvd.intro_left _ rfl

/-- (−2)^i is divisible by 2^i. -/
theorem two_pow_dvd_neg_two_pow (i : ℕ) : (2 : ℤ) ^ i ∣ (-2) ^ i := by
  rw [show (-2 : ℤ) = -1 * 2 by norm_num, mul_pow]
  exact Dvd.intro_left _ rfl

/-- The term of a tuple with more than ν − 1 + |J₁| marks is divisible by 2^ν. -/
theorem dvd_term {J₁ J₂ : Finset (Fin r)} (A : Fin r → Finset E) {S : Fin r → Finset E} (hS : S ∈ Fintype.piFinset (dom A (J₁ ∪ J₂))) {ν : ℕ}
    (hν : ν + #J₁ ≤ ∑ j, #(S j)) : (2 : ℤ) ^ ν ∣ ∏ j, fac J₁ J₂ j (S j) := by
  have h1 : ∀ j : Fin r, (2 : ℤ) ^ (#(S j) - if j ∈ J₁ then 1 else 0) ∣ fac J₁ J₂ j (S j) := by
    intro j
    unfold fac
    by_cases h1 : j ∈ J₁
    · simp only [if_pos h1]
      exact two_pow_dvd_sig _
    · by_cases h2 : j ∈ J₂
      · simp only [if_neg h1, if_pos h2, Nat.sub_zero]
        exact two_pow_dvd_neg_two_pow _
      · have h3 : j ∉ J₁ ∪ J₂ := fun h => (mem_union.1 h).elim h1 h2
        have h4 := Fintype.mem_piFinset.1 hS j
        rw [dom, if_neg h3, mem_singleton] at h4
        simp only [if_neg h1, if_neg h2, h4, card_empty, Nat.sub_zero, pow_zero]
        exact one_dvd _
  have h2 : ∑ j, #(S j) ≤ ∑ j : Fin r, (#(S j) - if j ∈ J₁ then 1 else 0) + #J₁ := by
    have h3 : #J₁ = ∑ j : Fin r, if j ∈ J₁ then 1 else 0 := by
      rw [sum_boole, filter_mem_eq_inter, univ_inter, Nat.cast_id]
    rw [h3, ← sum_add_distrib]
    exact sum_le_sum fun j _ => by omega
  refine (pow_dvd_pow 2 (by omega : ν ≤ ∑ j : Fin r, (#(S j) - if j ∈ J₁ then 1 else 0))).trans ?_
  rw [← prod_pow_eq_pow_sum]
  exact prod_dvd_prod_of_dvd _ _ fun j _ => h1 j

/-- The cut-off lemma for one ξ. -/
theorem cutoff_one {J₁ J₂ : Finset (Fin r)} (hJ : Disjoint J₁ J₂) (A : Fin r → Finset E) {ν M : ℕ} (hν : 1 ≤ ν) (hM : ν - 1 + #J₁ ≤ M) :
    (∏ j ∈ J₁, ev #(A j)) * ∏ j ∈ J₂, (-1 : ℤ) ^ #(A j) ≡
      ∑ S ∈ (Fintype.piFinset (dom A (J₁ ∪ J₂))).filter (fun S => ∑ j, #(S j) ≤ M), (∏ j ∈ J₁, sig #(S j)) * ∏ j ∈ J₂, (-2 : ℤ) ^ #(S j)
      [ZMOD 2 ^ ν] := by
  have h1 : ∀ S : Fin r → Finset E, (∏ j ∈ J₁, sig #(S j)) * ∏ j ∈ J₂, (-2 : ℤ) ^ #(S j) = ∏ j, fac J₁ J₂ j (S j) := fun S =>
    prod_mul_prod hJ _ _
  simp only [h1]
  rw [← sum_all hJ A, ← sum_filter_add_sum_filter_not (Fintype.piFinset (dom A (J₁ ∪ J₂))) fun S => ∑ j, #(S j) ≤ M]
  refine (Int.modEq_iff_dvd.2 ?_)
  rw [sub_add_cancel_left, dvd_neg]
  refine dvd_sum fun S hS => ?_
  obtain ⟨hS1, hS2⟩ := mem_filter.1 hS
  exact dvd_term A hS1 (by omega)

end Cutoff

end ClauseBound.ParityChecks.StepOne
