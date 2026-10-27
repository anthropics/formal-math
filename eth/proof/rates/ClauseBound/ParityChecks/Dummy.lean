/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ParityChecksStatement
public import Mathlib.Algebra.BigOperators.ModEq
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-! # Checks as dummy variables

[q even] = ½·Σ_{y ∈ {0,1}} (−1)^{y·q}. So a parity check j can be replaced by a new variable y_j:
the pair (e, j) of a clause e of check j counts as violated by (ξ, y) if ξ violates e and
y_j = 1. Then 2^r·∏_j [|V_j(ξ)| even] is the sum over y and over all sets S of violated pairs of
(−2)^|S| (`sum_dummy`), and the sets with more than M elements may be left out
modulo 2^{M+1} (`cutoff_dummy`). Different from Lemma 12 of the paper, which gives a set of q marks
in one check the weight σ_q: here every mark has the weight −2. -/

@[expose] public section

open Finset ParityChecks

namespace ClauseBound.ParityChecks.Dummy

variable {X E : Type} [Fintype X] [Fintype E] [DecidableEq E]

/-- The incidences (e, j) that (ξ, y) violates: e ∈ Λ_j ∩ V(ξ), j ∈ J₁ ∪ J₂, and y_j = 1 if j ∈ J₁. -/
def inc (V : X → Finset E) (r : ℕ) (Λ : ℕ → Finset E) (J₁ J₂ : Finset (Fin r)) (ξ : X) (y : Fin r → Bool) : Finset (E × Fin r) :=
  univ.filter fun q => q.1 ∈ Λ q.2 ∩ V ξ ∧ ((q.2 ∈ J₁ ∧ y q.2 = true) ∨ q.2 ∈ J₂)

/-- Σ_{S ⊆ T} (−2)^|S| = (−1)^|T|. -/
theorem sum_powerset_neg_two {α : Type} (T : Finset α) : ∑ S ∈ T.powerset, (-2 : ℤ) ^ #S = (-1) ^ #T := by
  have h := sum_pow_mul_eq_add_pow (-2 : ℤ) 1 T
  simp only [one_pow, mul_one] at h
  rw [h]
  norm_num

omit [Fintype X] in
/-- The number of violated incidences, check by check. -/
theorem card_inc (V : X → Finset E) (r : ℕ) (Λ : ℕ → Finset E) (J₁ J₂ : Finset (Fin r)) (ξ : X) (y : Fin r → Bool) :
    #(inc V r Λ J₁ J₂ ξ y) = ∑ j : Fin r, if (j ∈ J₁ ∧ y j = true) ∨ j ∈ J₂ then #(Λ j ∩ V ξ) else 0 := by
  rw [inc, card_filter, Fintype.sum_prod_type_right]
  refine sum_congr rfl fun j _ => ?_
  by_cases hc : (j ∈ J₁ ∧ y j = true) ∨ j ∈ J₂
  · simp only [hc, and_true, if_true]
    rw [← card_filter, filter_mem_eq_inter, univ_inter]
  · simp only [hc, and_false, if_false, sum_const_zero]

/-- The factor of check j, as a function of the value b of its dummy variable. -/
def fac (V : X → Finset E) (r : ℕ) (Λ : ℕ → Finset E) (J₁ J₂ : Finset (Fin r)) (ξ : X) (j : Fin r) (b : Bool) : ℤ :=
  if (j ∈ J₁ ∧ b = true) ∨ j ∈ J₂ then (-1) ^ #(Λ j ∩ V ξ) else 1

omit [Fintype X] in
theorem neg_one_pow_card_inc (V : X → Finset E) (r : ℕ) (Λ : ℕ → Finset E) (J₁ J₂ : Finset (Fin r)) (ξ : X) (y : Fin r → Bool) :
    (-1 : ℤ) ^ #(inc V r Λ J₁ J₂ ξ y) = ∏ j, fac V r Λ J₁ J₂ ξ j (y j) := by
  rw [card_inc, ← prod_pow_eq_pow_sum]
  refine prod_congr rfl fun j _ => ?_
  unfold fac
  split_ifs
  · rfl
  · exact pow_zero _

/-- 1 + (−1)^q = 2·[q even]. -/
theorem one_add_neg_one_pow (q : ℕ) : (-1 : ℤ) ^ q + 1 = 2 * ev q := by
  unfold ev
  rcases Nat.even_or_odd q with h | h
  · rw [h.neg_one_pow, if_pos h]; norm_num
  · rw [h.neg_one_pow, if_neg (Nat.not_even_iff_odd.2 h)]; norm_num

omit [Fintype X] [Fintype E] in
/-- The two values of the dummy variable of check j together. -/
theorem sum_fac (V : X → Finset E) (r : ℕ) (Λ : ℕ → Finset E) (J₁ J₂ : Finset (Fin r)) (h : Disjoint J₁ J₂) (ξ : X) (j : Fin r) :
    ∑ b : Bool, fac V r Λ J₁ J₂ ξ j b =
      2 * ((if j ∈ J₁ then ev #(Λ j ∩ V ξ) else 1) * if j ∈ J₂ then (-1 : ℤ) ^ #(Λ j ∩ V ξ) else 1) := by
  rw [Fintype.sum_bool]
  unfold fac
  by_cases h1 : j ∈ J₁
  · have h2 : j ∉ J₂ := disjoint_left.1 h h1
    simp only [h1, h2, true_and, or_false, if_true, if_false, Bool.false_eq_true, mul_one]
    exact one_add_neg_one_pow _
  · by_cases h2 : j ∈ J₂
    · simp only [h1, h2, false_and, or_true, if_true, if_false, one_mul]
      ring
    · simp only [h1, h2, false_and, or_false, if_false, mul_one]
      norm_num

omit [Fintype X] in
/-- 2^r·∏_{j ∈ J₁} [|V_j(ξ)| even]·∏_{j ∈ J₂} (−1)^{|V_j(ξ)|} is the sum over the dummy variables y
and over all sets S of violated incidences of (−2)^|S|. -/
theorem sum_dummy (V : X → Finset E) (r : ℕ) (Λ : ℕ → Finset E) (J₁ J₂ : Finset (Fin r)) (h : Disjoint J₁ J₂) (ξ : X) :
    ∑ y : Fin r → Bool, ∑ S ∈ (inc V r Λ J₁ J₂ ξ y).powerset, (-2 : ℤ) ^ #S =
      2 ^ r * ((∏ j ∈ J₁, ev #(Λ j ∩ V ξ)) * ∏ j ∈ J₂, (-1 : ℤ) ^ #(Λ j ∩ V ξ)) := by
  simp only [sum_powerset_neg_two, neg_one_pow_card_inc]
  rw [← Fintype.piFinset_univ, ← prod_univ_sum]
  simp only [sum_fac V r Λ J₁ J₂ h ξ]
  rw [prod_mul_distrib, prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, Fintype.prod_ite_mem, Fintype.prod_ite_mem]

/-- A power of −2 with an exponent above M vanishes modulo 2^{M+1}. -/
theorem neg_two_pow_modEq {M k : ℕ} : (-2 : ℤ) ^ k ≡ (if k ≤ M then (-2 : ℤ) ^ k else 0) [ZMOD 2 ^ (M + 1)] := by
  split_ifs with hk
  · exact Int.ModEq.refl _
  · refine Int.modEq_zero_iff_dvd.2 ?_
    exact (pow_dvd_pow_of_dvd (by norm_num : (2 : ℤ) ∣ -2) (M + 1)).trans (pow_dvd_pow _ (by omega))

/-- The cut-off lemma with dummy variables: modulo 2^{M+1} only the sets of at most M violated
incidences count. -/
theorem cutoff_dummy (V : X → Finset E) (r : ℕ) (Λ : ℕ → Finset E) (J₁ J₂ : Finset (Fin r)) (h : Disjoint J₁ J₂) (f : X → ℤ) (M : ℕ) :
    2 ^ r * (∑ ξ, f ξ * (∏ j ∈ J₁, ev #(Λ j ∩ V ξ)) * ∏ j ∈ J₂, (-1 : ℤ) ^ #(Λ j ∩ V ξ)) ≡
      ∑ ξ, f ξ * ∑ y : Fin r → Bool, ∑ S ∈ (inc V r Λ J₁ J₂ ξ y).powerset with #S ≤ M, (-2 : ℤ) ^ #S [ZMOD 2 ^ (M + 1)] := by
  rw [mul_sum]
  refine Int.ModEq.sum fun ξ _ => ?_
  have e : 2 ^ r * (f ξ * (∏ j ∈ J₁, ev #(Λ j ∩ V ξ)) * ∏ j ∈ J₂, (-1 : ℤ) ^ #(Λ j ∩ V ξ)) =
      f ξ * ∑ y : Fin r → Bool, ∑ S ∈ (inc V r Λ J₁ J₂ ξ y).powerset, (-2 : ℤ) ^ #S := by
    rw [sum_dummy V r Λ J₁ J₂ h ξ]
    ring
  rw [e]
  refine Int.ModEq.mul_left _ (Int.ModEq.sum fun y _ => ?_)
  rw [sum_filter]
  exact Int.ModEq.sum fun S _ => neg_two_pow_modEq

end ClauseBound.ParityChecks.Dummy
