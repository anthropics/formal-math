/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Variance.Defs
public import Eight.SecNetworks_Grouping
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # The indicators of the ordered pairs

«Each ordered pair (a,b) contributes with probability 1/K² … The indicators of two ordered pairs
have covariance 0 if the pairs are disjoint and at most 1 otherwise, and by (i) the ordered pairs
that meet a fixed pair have c-values summing to at most 4P.» (Proof of Lemma 1.)
The three facts behind these sentences are `Eight.SecNetworks.pair_prob`, `cov_disjoint` and
`meeting_le` (proof/networks/Eight/SecNetworks_Grouping.lean); here they are brought into the form
of proof/networks/Variance/Defs.lean, and Y is written as the sum of c_{a,b} over the ordered pairs
that contribute. -/

public section

namespace Variance

open Finset Eight.SecNetworks

/-- A sum over the ordered pairs of distinct nodes, as a double sum. -/
theorem sum_ordered {g : ℕ} {X : Type} [AddCommMonoid X] (F : Fin g × Fin g → X) : ∑ p ∈ ordered g, F p = ∑ a, ∑ b ∈ univ.erase a, F (a, b) := by
  unfold ordered
  rw [sum_filter, Fintype.sum_prod_type]
  refine sum_congr rfl fun a _ => ?_
  rw [← filter_ne' univ a, sum_filter]
  refine sum_congr rfl fun b _ => ?_
  by_cases h : a = b
  · simp [h]
  · simp [h, Ne.symm h]

/-- The total U is the sum of c_{a,b} over the ordered pairs. -/
theorem sum_ordered_c {g : ℕ} (c : Fin g → Fin g → ℕ) : ∑ p ∈ ordered g, c p.1 p.2 = ∑ a, ∑ b ∈ univ.erase a, c a b := sum_ordered fun p => c p.1 p.2

/-- Y_{γ,γ'} is the sum of c_{a,b} over the ordered pairs that contribute. -/
theorem stYIsSum : StYIsSum := by
  intro g K c χ γ γ' hne
  rw [sum_ordered]
  unfold Y
  rw [sum_filter]
  refine sum_congr rfl fun a _ => ?_
  by_cases ha : χ a = γ
  · rw [if_pos ha, sum_filter, ← add_sum_erase _ _ (mem_univ a), if_neg (by rw [ha]; exact hne), zero_add]
    exact sum_congr rfl fun b _ => by simp [Contributes, ha]
  · rw [if_neg ha]
    exact (sum_eq_zero fun b _ => by simp [Contributes, ha]).symm

/-- «Each ordered pair (a,b) contributes with probability 1/K²». -/
theorem stPairProb : StPairProb := by
  intro g K γ γ' p hp
  exact pair_prob (mem_filter.1 hp).2 γ γ'

/-- «The indicators of two ordered pairs have covariance 0 if the pairs are disjoint»: both
contribute with probability 1/K⁴ = (1/K²)·(1/K²). -/
theorem stCovDisjoint : StCovDisjoint := by
  intro g K γ γ' p hp q hq hm
  have hp' : p.1 ≠ p.2 := (mem_filter.1 hp).2
  have hq' : q.1 ≠ q.2 := (mem_filter.1 hq).2
  obtain ⟨h1, h2, h3, h4⟩ : q.1 ≠ p.1 ∧ q.1 ≠ p.2 ∧ q.2 ≠ p.1 ∧ q.2 ≠ p.2 := by
    refine ⟨fun h => hm (.inl h), fun h => hm (.inr (.inl h)), fun h => hm (.inr (.inr (.inl h))), fun h => hm (.inr (.inr (.inr h)))⟩
  have h := cov_disjoint hp' h1.symm h3.symm h2.symm h4.symm hq' γ γ'
  unfold cov
  have h' : ((#{χ : Fin g → Fin K | (χ p.1 = γ ∧ χ p.2 = γ') ∧ (χ q.1 = γ ∧ χ q.2 = γ')} : ℕ) : ℤ) * (K : ℤ) ^ 4 = (K : ℤ) ^ g := by exact_mod_cast h
  linarith

/-- «and at most 1 otherwise»: an event has probability at most 1. -/
theorem stCovLeOne : StCovLeOne := by
  intro g K γ γ' p q
  unfold cov
  have h1 : #{χ : Fin g → Fin K | Contributes γ γ' χ p ∧ Contributes γ γ' χ q} ≤ K ^ g := by
    calc _ ≤ #(univ : Finset (Fin g → Fin K)) := card_le_card (filter_subset _ _)
      _ = K ^ g := by simp
  have h2 : ((#{χ : Fin g → Fin K | Contributes γ γ' χ p ∧ Contributes γ γ' χ q} : ℕ) : ℤ) ≤ (K : ℤ) ^ g := by exact_mod_cast h1
  have h3 : (0 : ℤ) ≤ (K : ℤ) ^ 4 := by positivity
  have h4 : (0 : ℤ) ≤ (K : ℤ) ^ g := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 h3]

/-- «by (i) the ordered pairs that meet a fixed pair have c-values summing to at most 4P». -/
theorem stMeeting : StMeeting := by
  intro g P c hs hP p
  refine le_trans (le_of_eq ?_) (meeting_le hs hP p)
  unfold ordered
  rw [filter_filter]

end Variance
