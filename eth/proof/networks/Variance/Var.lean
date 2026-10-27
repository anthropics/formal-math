/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Variance.Cov
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # The mean and the variance of Y, along the printed sentences

«Each ordered pair (a,b) contributes with probability 1/K², so 𝔼Y_{γ,γ'} = U/K². … Hence Var
Y_{γ,γ'} ≤ Σ_{(a,b)∈[g]²: a≠b} c_{a,b}·4P = 4PU» (proof of Lemma 1). Y is the sum of c_{a,b} times
the indicator of (a,b). So its mean is the sum of c_{a,b} times the probability of (a,b)
(`stSoMean`), and its variance is the sum of
c_p·c_q times the covariance of the indicators of p and q (`stVarIsSumOfCov`). The step «Hence»
(`stHence`) holds for any numbers in the place of the covariances that vanish for disjoint pairs and
are bounded otherwise. `stVarOf` puts the sentences together. The two moments of
proof/networks/Groundwork/Net/Colouring.lean are not used. -/

public section

namespace Variance

open Finset Eight.SecNetworks

/-- «so 𝔼Y_{γ,γ'} = U/K²», from the two statements before it: Y_{γ,γ'} is the sum of c_{a,b} over
the ordered pairs (a, b) that contribute (`StYIsSum`), and «Each ordered pair (a,b) contributes with
probability 1/K²» (`StPairProb`). -/
theorem stSoMean : StSoMean := by
  intro hY hP g K c γ γ' hne
  have h1 : ∑ χ : Fin g → Fin K, Y c χ γ γ' = ∑ p ∈ ordered g, c p.1 p.2 * #{χ : Fin g → Fin K | Contributes γ γ' χ p} := by
    simp only [hY g K c _ γ γ' hne]
    rw [sum_comm]
    refine sum_congr rfl fun p _ => ?_
    rw [← sum_filter, sum_const, smul_eq_mul, mul_comm]
  rw [h1, sum_mul, ← sum_ordered_c, mul_sum]
  refine sum_congr rfl fun p hp => ?_
  rw [mul_assoc, hP g K γ γ' p hp, mul_comm]

/-- «so 𝔼Y_{γ,γ'} = U/K²». -/
theorem stMean : StMean := stSoMean stYIsSum stPairProb

/-- The variance of Y is the sum of c_p·c_q·Cov(p, q) over all pairs of ordered pairs. -/
theorem stVarIsSumOfCov : StVarIsSumOfCov := by
  intro g K c γ γ' hne
  have hM := stMean g K c γ γ' hne
  rw [← sum_ordered_c] at hM ⊢
  have hy : ∀ χ : Fin g → Fin K, ((Y c χ γ γ' : ℕ) : ℤ) = ∑ p ∈ ordered g, ((c p.1 p.2 : ℕ) : ℤ) * (if Contributes γ γ' χ p then 1 else 0) := by
    intro χ
    rw [stYIsSum g K c χ γ γ' hne]
    push_cast
    refine sum_congr rfl fun p _ => ?_
    split_ifs <;> simp
  have hsq : ∑ χ : Fin g → Fin K, ((Y c χ γ γ' : ℕ) : ℤ) ^ 2
      = ∑ p ∈ ordered g, ∑ q ∈ ordered g, ((c p.1 p.2 : ℕ) : ℤ) * ((c q.1 q.2 : ℕ) : ℤ) * (#{χ : Fin g → Fin K | Contributes γ γ' χ p ∧ Contributes γ γ' χ q} : ℕ) := by
    simp only [hy, sq, sum_mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun p _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun q _ => ?_
    rw [card_filter]
    push_cast
    rw [mul_sum]
    refine sum_congr rfl fun χ _ => ?_
    by_cases h1 : Contributes γ γ' χ p
    · by_cases h2 : Contributes γ γ' χ q
      · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩]
        ring
      · rw [if_neg h2, if_neg (show ¬ (Contributes γ γ' χ p ∧ Contributes γ γ' χ q) from fun h => h2 h.2)]
        ring
    · rw [if_neg h1, if_neg (show ¬ (Contributes γ γ' χ p ∧ Contributes γ γ' χ q) from fun h => h1 h.1)]
      ring
  have hUU : (((∑ p ∈ ordered g, c p.1 p.2 : ℕ) : ℤ)) ^ 2 = ∑ p ∈ ordered g, ∑ q ∈ ordered g, ((c p.1 p.2 : ℕ) : ℤ) * ((c q.1 q.2 : ℕ) : ℤ) := by
    push_cast
    rw [sq, sum_mul_sum]
  have hM' : (∑ χ : Fin g → Fin K, ((Y c χ γ γ' : ℕ) : ℤ)) * (K : ℤ) ^ 2 = (K : ℤ) ^ g * ((∑ p ∈ ordered g, c p.1 p.2 : ℕ) : ℤ) := by exact_mod_cast hM
  have hcard : (∑ _χ : Fin g → Fin K, (1 : ℤ)) = (K : ℤ) ^ g := by simp
  generalize ((∑ p ∈ ordered g, c p.1 p.2 : ℕ) : ℤ) = U at hUU hM' ⊢
  have hL : ∑ χ : Fin g → Fin K, (((K ^ 2 : ℕ) : ℤ) * ((Y c χ γ γ' : ℕ) : ℤ) - U) ^ 2
      = (K : ℤ) ^ 4 * ∑ χ : Fin g → Fin K, ((Y c χ γ γ' : ℕ) : ℤ) ^ 2 - 2 * U * ((∑ χ : Fin g → Fin K, ((Y c χ γ γ' : ℕ) : ℤ)) * (K : ℤ) ^ 2) + U ^ 2 * ∑ _χ : Fin g → Fin K, (1 : ℤ) := by
    rw [mul_sum, sum_mul, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun χ _ => ?_
    push_cast
    ring
  have hR : ∑ p ∈ ordered g, ∑ q ∈ ordered g, ((c p.1 p.2 : ℕ) : ℤ) * ((c q.1 q.2 : ℕ) : ℤ) * cov γ γ' p q
      = (K : ℤ) ^ 4 * (∑ p ∈ ordered g, ∑ q ∈ ordered g, ((c p.1 p.2 : ℕ) : ℤ) * ((c q.1 q.2 : ℕ) : ℤ) * (#{χ : Fin g → Fin K | Contributes γ γ' χ p ∧ Contributes γ γ' χ q} : ℕ))
        - (K : ℤ) ^ g * ∑ p ∈ ordered g, ∑ q ∈ ordered g, ((c p.1 p.2 : ℕ) : ℤ) * ((c q.1 q.2 : ℕ) : ℤ) := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun p _ => ?_
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun q _ => ?_
    unfold cov
    ring
  rw [hL, hR, hM', hcard, hsq, ← hUU]
  ring

/-- **«Hence»**, for any numbers κ(p, q) in the place of the covariances: if κ vanishes for disjoint
pairs, κ(p, q) ≤ m for all pairs and m ≥ 0, then Σ_p Σ_q c_p·c_q·κ(p, q) ≤ Σ_p c_p·4P·m = 4PU·m, for
c symmetric with (i) of Definition 2. -/
theorem stHence : StHence := by
  intro g P c hs hP κ m hm h0 h1
  have hrow : ∀ p ∈ ordered g, ∑ q ∈ ordered g, ((c p.1 p.2 : ℕ) : ℤ) * ((c q.1 q.2 : ℕ) : ℤ) * κ p q ≤ ((c p.1 p.2 : ℕ) : ℤ) * (((4 * P : ℕ) : ℤ) * m) := by
    intro p hp
    have hsplit : ∑ q ∈ ordered g, ((c p.1 p.2 : ℕ) : ℤ) * ((c q.1 q.2 : ℕ) : ℤ) * κ p q = ∑ q ∈ ordered g with Meets p q, ((c p.1 p.2 : ℕ) : ℤ) * ((c q.1 q.2 : ℕ) : ℤ) * κ p q := by
      rw [sum_filter]
      refine sum_congr rfl fun q hq => ?_
      by_cases h : Meets p q
      · rw [if_pos h]
      · rw [if_neg h, h0 p hp q hq h, mul_zero]
    rw [hsplit]
    calc ∑ q ∈ ordered g with Meets p q, ((c p.1 p.2 : ℕ) : ℤ) * ((c q.1 q.2 : ℕ) : ℤ) * κ p q
        ≤ ∑ q ∈ ordered g with Meets p q, ((c p.1 p.2 : ℕ) : ℤ) * ((c q.1 q.2 : ℕ) : ℤ) * m :=
          sum_le_sum fun q _ => mul_le_mul_of_nonneg_left (h1 p q) (by positivity)
      _ = ((c p.1 p.2 : ℕ) : ℤ) * (((∑ q ∈ ordered g with Meets p q, c q.1 q.2 : ℕ) : ℤ) * m) := by
          push_cast
          rw [sum_mul, mul_sum]
          exact sum_congr rfl fun q _ => by ring
      _ ≤ ((c p.1 p.2 : ℕ) : ℤ) * (((4 * P : ℕ) : ℤ) * m) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by exact_mod_cast stMeeting g P c hs hP p) hm) (by positivity)
  calc ∑ p ∈ ordered g, ∑ q ∈ ordered g, ((c p.1 p.2 : ℕ) : ℤ) * ((c q.1 q.2 : ℕ) : ℤ) * κ p q
      ≤ ∑ p ∈ ordered g, ((c p.1 p.2 : ℕ) : ℤ) * (((4 * P : ℕ) : ℤ) * m) := sum_le_sum hrow
    _ = ((4 * P * (∑ a, ∑ b ∈ univ.erase a, c a b) : ℕ) : ℤ) * m := by
        rw [← sum_ordered_c, ← sum_mul]
        push_cast
        ring

/-- «Hence Var Y_{γ,γ'} ≤ 4PU», put together from the sentences before it. -/
theorem stVarOf : StVarOf := by
  intro hV hD hO hH g K P c hs hP γ γ' hne
  rw [hV g K c γ γ' hne]
  refine (hH g P c hs hP (cov γ γ') ((K : ℤ) ^ 4 * (K : ℤ) ^ g) (by positivity) (hD g K γ γ') (hO g K γ γ')).trans (le_of_eq ?_)
  push_cast
  ring

/-- «Hence Var Y_{γ,γ'} ≤ Σ_{(a,b)∈[g]²: a≠b} c_{a,b}·4P = 4PU». -/
theorem stVar : StVar := stVarOf stVarIsSumOfCov stCovDisjoint stCovLeOne stHence

end Variance
