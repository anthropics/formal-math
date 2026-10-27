/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.SecNetworks_Defs
import all Groundwork.Net.Colouring

/-! # Proof of Lemma 1, «A good grouping exists»: every sentence with the paper's numbers

The paragraph chooses χ(a) ∈ [K] independently and uniformly for each of the g nodes. Here **probabilities
are rendered as counts** over the K^g groupings χ : [g] → [K], with denominators cleared:
«Pr(E) ≤ p» reads #{χ | E} ≤ p·K^g, «𝔼X = m» reads Σ_χ X(χ) = m·K^g, and «Var X ≤ v» reads Σ_χ (X(χ)
− m)² ≤ v·K^g. No measure theory is used.

The sentences, in the order of the text: `Y_symm`, `pair_prob`, `mean_Y`, `cov_disjoint`,
`meeting_le`, `var_Y`, `total_le`, `cheb_Y`, `card_pairs_lt`, `some_pair`, `mean_size`, `var_size`,
`cheb_size`, `some_group`,
and the closing theorem `groupingFacts : GroupingFacts` (g = 3K⁸: 4/(3K²), < 2/3, K/g, < 1/3, a good
grouping exists).

The two moments of Y and of the size of a group are taken from
proof/networks/Groundwork/Net/Colouring.lean, which counts groupings with prescribed values;
`pair_prob`, `cov_disjoint` and `meeting_le` state in the paper's words the three lemmas on which
its moments of Y rest (`card_two`, `card_four`, `sum_meet`) and are not used again below. Its bound
on the variance of Y, 4PU/K², is sharper than the 4PU of the paper
(a pair that meets a fixed pair is given covariance at most 1/K² there, at most 1 in the paper);
`var_Y` states the paper's 4PU, and both uses of Chebyshev and all three union bounds below are made
from the paper's numbers. -/

public section

namespace Eight.SecNetworks

open Finset Groundwork.Colouring

variable {g K : ℕ}

/-! ### Passage to the lemmas on counts (which want c_{a,a} = 0) -/

/-- The numbers c_{a,b} with 0 on the diagonal. -/
private def off (c : Fin g → Fin g → ℕ) (a b : Fin g) : ℕ := if b ≠ a then c a b else 0

private theorem off_diag (c : Fin g → Fin g → ℕ) (a : Fin g) : off c a a = 0 := by simp [off]

private theorem off_symm {c : Fin g → Fin g → ℕ} (hs : ∀ a b, c a b = c b a) (a b : Fin g) : off c a b = off c b a := by
  simp only [off, hs a b, ne_comm]

private theorem off_row (c : Fin g → Fin g → ℕ) (a : Fin g) : ∑ b, off c a b = ∑ b ∈ univ.erase a, c a b := by
  unfold off
  rw [← sum_filter, filter_ne']

private theorem Us_off (c : Fin g → Fin g → ℕ) : Us (off c) = ∑ a, ∑ b ∈ univ.erase a, c a b := by
  unfold Us
  rw [Fintype.sum_prod_type]
  exact sum_congr rfl fun a _ => off_row c a

private theorem Ys_off (c : Fin g → Fin g → ℕ) {γ γ' : Fin K} (hne : γ ≠ γ') (χ : Fin g → Fin K) : Ys (off c) γ γ' χ = Y c χ γ γ' := by
  unfold Ys Y off
  rw [Fintype.sum_prod_type, sum_filter]
  refine sum_congr rfl fun a _ => ?_
  by_cases ha : χ a = γ
  · rw [if_pos ha, sum_filter]
    refine sum_congr rfl fun b _ => ?_
    by_cases hb : χ b = γ'
    · have hba : b ≠ a := by
        rintro rfl
        exact hne (ha.symm.trans hb)
      simp [ha, hb, hba]
    · simp [hb]
  · simp [ha]

/-- From the first two moments to the variance, denominators cleared: if Σ Y·A = N·m and Σ Y²·A² ≤
N·m² + V, over N points, then Σ (A·Y − m)² ≤ V. -/
private theorem var_of_moments {Ω : Type} [Fintype Ω] (X : Ω → ℕ) (A m V : ℕ) (S1 : (∑ χ, X χ) * A = Fintype.card Ω * m)
    (S2 : (∑ χ, X χ ^ 2) * A ^ 2 ≤ Fintype.card Ω * m ^ 2 + V) : ∑ χ, ((A : ℤ) * X χ - m) ^ 2 ≤ V := by
  zify at S1 S2
  have hsum : ∑ χ : Ω, ((A : ℤ) * X χ - m) ^ 2 = (∑ χ : Ω, (X χ : ℤ) ^ 2) * A ^ 2 - 2 * m * ((∑ χ : Ω, (X χ : ℤ)) * A) + (Fintype.card Ω : ℤ) * m ^ 2 := by
    have : ∀ χ : Ω, ((A : ℤ) * X χ - m) ^ 2 = (X χ : ℤ) ^ 2 * A ^ 2 - 2 * m * ((X χ : ℤ) * A) + (m : ℤ) ^ 2 := by
      intro χ; ring
    simp only [this, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← mul_sum, sum_const, card_univ, nsmul_eq_mul]
  rw [hsum, S1]
  linarith

/-- Chebyshev's inequality as a count, denominators cleared: if Σ (A·X − m)² ≤ V, then the number of
points with t·(A·X − m) > s, times s², is at most t²·V. -/
private theorem cheb_count {Ω : Type} [Fintype Ω] (X : Ω → ℕ) (A m V t s : ℕ) (hV : ∑ χ, ((A : ℤ) * X χ - m) ^ 2 ≤ V) :
    #{χ : Ω | t * m + s < t * (A * X χ)} * s ^ 2 ≤ t ^ 2 * V := by
  have hc := cheb (fun χ : Ω => (t : ℤ) * ((A : ℤ) * X χ - m)) s (by positivity)
  have hsub : #{χ : Ω | t * m + s < t * (A * X χ)} ≤ #{χ : Ω | (s : ℤ) ≤ (t : ℤ) * ((A : ℤ) * X χ - m)} := by
    refine card_le_card fun χ h => ?_
    simp only [mem_filter, mem_univ, true_and] at h ⊢
    zify at h
    linarith
  have hsum : ∑ χ : Ω, ((t : ℤ) * ((A : ℤ) * X χ - m)) ^ 2 = (t : ℤ) ^ 2 * ∑ χ : Ω, ((A : ℤ) * X χ - m) ^ 2 := by
    simp only [mul_pow, mul_sum]
  rw [hsum] at hc
  have a1 : (#{χ : Ω | t * m + s < t * (A * X χ)} : ℤ) * (s : ℤ) ^ 2 ≤ (#{χ : Ω | (s : ℤ) ≤ (t : ℤ) * ((A : ℤ) * X χ - m)} : ℤ) * (s : ℤ) ^ 2 :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.2 hsub) (sq_nonneg _)
  have a2 : (t : ℤ) ^ 2 * ∑ χ : Ω, ((A : ℤ) * X χ - m) ^ 2 ≤ (t : ℤ) ^ 2 * V := mul_le_mul_of_nonneg_left hV (sq_nonneg _)
  have a3 := a1.trans (hc.trans a2)
  exact_mod_cast a3

/-! ### The shared bits between two groups -/

/-- «let Y_{γ,γ'} = Y_{γ',γ} be the sum of c_{a,b} over all a ∈ G_γ and b ∈ G_{γ'}»: the equality,
from c_{a,b} = c_{b,a}. -/
theorem Y_symm {c : Fin g → Fin g → ℕ} (hs : ∀ a b, c a b = c b a) (χ : Fin g → Fin K) (γ γ' : Fin K) : Y c χ γ γ' = Y c χ γ' γ := by
  unfold Y
  rw [sum_comm]
  exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => hs _ _

/-- «Each ordered pair (a,b) contributes with probability 1/K²». -/
theorem pair_prob {a b : Fin g} (hab : a ≠ b) (γ γ' : Fin K) : #{χ : Fin g → Fin K | χ a = γ ∧ χ b = γ'} * K ^ 2 = K ^ g := by
  simpa only [Fintype.card_fin] using card_two (κ := Fin K) hab γ γ'

/-- «so 𝔼Y_{γ,γ'} = U/K²». -/
theorem mean_Y (c : Fin g → Fin g → ℕ) {γ γ' : Fin K} (hne : γ ≠ γ') :
    (∑ χ : Fin g → Fin K, Y c χ γ γ') * K ^ 2 = K ^ g * ∑ a, ∑ b ∈ univ.erase a, c a b := by
  have h := sum_Ys (κ := Fin K) (off c) (off_diag c) γ γ'
  simpa only [Fintype.card_fin, Ys_off c hne, Us_off] using h

/-- «The indicators of two ordered pairs have covariance 0 if the pairs are disjoint»: both pairs
contribute with probability 1/K⁴ = (1/K²)·(1/K²). («and at most 1 otherwise» needs no proof:
indicators are at most 1.) -/
theorem cov_disjoint {a b a' b' : Fin g} (hab : a ≠ b) (h1 : a ≠ a') (h2 : a ≠ b') (h3 : b ≠ a') (h4 : b ≠ b') (h5 : a' ≠ b') (γ γ' : Fin K) :
    #{χ : Fin g → Fin K | (χ a = γ ∧ χ b = γ') ∧ (χ a' = γ ∧ χ b' = γ')} * K ^ 4 = K ^ g := by
  simpa only [Fintype.card_fin] using card_four (κ := Fin K) hab h1 h2 h3 h4 h5 γ γ'

/-- «by (i) the ordered pairs that meet a fixed pair have c-values summing to at most 4P». -/
theorem meeting_le {c : Fin g → Fin g → ℕ} (hs : ∀ a b, c a b = c b a) {P : ℕ} (hP : ∀ a, ∑ b ∈ univ.erase a, c a b ≤ P) (p : Fin g × Fin g) :
    ∑ q : Fin g × Fin g with q.1 ≠ q.2 ∧ (q.1 = p.1 ∨ q.1 = p.2 ∨ q.2 = p.1 ∨ q.2 = p.2), c q.1 q.2 ≤ 4 * P := by
  refine le_trans ?_ (sum_meet (off c) (off_symm hs) P (fun a => by rw [off_row]; exact hP a) p)
  rw [sum_filter]
  refine sum_le_sum fun q _ => ?_
  split_ifs with h
  · obtain ⟨hq, hm⟩ := h
    have e : off c q.1 q.2 = c q.1 q.2 := by simp [off, hq.symm]
    have hm1 : 1 ≤ meet p q := by
      unfold meet
      rcases hm with h | h | h | h <;> simp only [h, if_true] <;> omega
    rw [e]
    exact Nat.le_mul_of_pos_right _ hm1
  · exact Nat.zero_le _

/-- «Hence Var Y_{γ,γ'} ≤ Σ_{(a,b) : a ≠ b} c_{a,b}·4P = 4PU»: Σ_χ (Y − U/K²)² ≤ 4PU·K^g, multiplied
by K⁴. -/
theorem var_Y {c : Fin g → Fin g → ℕ} (hs : ∀ a b, c a b = c b a) {P : ℕ} (hP : ∀ a, ∑ b ∈ univ.erase a, c a b ≤ P) {γ γ' : Fin K} (hne : γ ≠ γ') :
    ∑ χ : Fin g → Fin K, (((K ^ 2 : ℕ) : ℤ) * (Y c χ γ γ' : ℕ) - ((∑ a, ∑ b ∈ univ.erase a, c a b : ℕ) : ℤ)) ^ 2
      ≤ ((4 * P * (∑ a, ∑ b ∈ univ.erase a, c a b) * K ^ 4 * K ^ g : ℕ) : ℤ) := by
  have S1 := mean_Y c hne
  have S2 := sum_Ys_sq (κ := Fin K) (off c) (off_diag c) (off_symm hs) P (fun a => by rw [off_row]; exact hP a) γ γ'
  simp only [Fintype.card_fin, Ys_off c hne, Us_off] at S2
  generalize (∑ a, ∑ b ∈ univ.erase a, c a b) = U at S1 S2 ⊢
  refine var_of_moments (fun χ : Fin g → Fin K => Y c χ γ γ') (K ^ 2) U _ (by simpa using S1) ?_
  rw [← pow_mul]
  have h2 : K ^ 2 ≤ K ^ 4 := by
    rcases Nat.eq_zero_or_pos K with h | h
    · simp [h]
    · exact Nat.pow_le_pow_right h (by omega)
  calc (∑ χ : Fin g → Fin K, Y c χ γ γ' ^ 2) * K ^ (2 * 2) ≤ K ^ g * U ^ 2 + 4 * K ^ 2 * K ^ g * P * U := S2
    _ = K ^ g * U ^ 2 + 4 * P * U * K ^ 2 * K ^ g := by ring
    _ ≤ K ^ g * U ^ 2 + 4 * P * U * K ^ 4 * K ^ g := by gcongr
    _ = Fintype.card (Fin g → Fin K) * U ^ 2 + 4 * P * U * K ^ 4 * K ^ g := by simp

/-- «4PU ≤ 4gP²»: U ≤ gP, by (i). -/
theorem total_le {c : Fin g → Fin g → ℕ} {P : ℕ} (hP : ∀ a, ∑ b ∈ univ.erase a, c a b ≤ P) : ∑ a, ∑ b ∈ univ.erase a, c a b ≤ g * P := by
  calc ∑ a, ∑ b ∈ univ.erase a, c a b ≤ ∑ _a : Fin g, P := sum_le_sum fun a _ => hP a
    _ = g * P := by simp

/-- «and by Chebyshev Pr(Y_{γ,γ'} > U/K² + gP/K³) ≤ 4K⁶/g», for every g. The event is multiplied by
K³. Proved from `var_Y` and `total_le`: the deviation is gP/K³, so the bound is 4gP²·K⁶/(gP)². -/
theorem cheb_Y {c : Fin g → Fin g → ℕ} (hs : ∀ a b, c a b = c b a) {P : ℕ} (hP : ∀ a, ∑ b ∈ univ.erase a, c a b ≤ P) {γ γ' : Fin K} (hne : γ ≠ γ') :
    g * #{χ : Fin g → Fin K | K * (∑ a, ∑ b ∈ univ.erase a, c a b) + g * P < K ^ 3 * Y c χ γ γ'} ≤ 4 * K ^ 6 * K ^ g := by
  have hV := var_Y hs hP hne
  have hU := total_le hP
  have hY : ∀ χ : Fin g → Fin K, Y c χ γ γ' ≤ ∑ a, ∑ b ∈ univ.erase a, c a b := fun χ => by
    rw [← Ys_off c hne, ← Us_off]
    exact Ys_le_Us _ _ _ _
  generalize (∑ a, ∑ b ∈ univ.erase a, c a b) = U at hV hU hY ⊢
  rcases Nat.eq_zero_or_pos (g * P) with h0 | hpos
  · have hU0 : U = 0 := by omega
    have : ({χ : Fin g → Fin K | K * U + g * P < K ^ 3 * Y c χ γ γ'} : Finset (Fin g → Fin K)) = ∅ := by
      refine filter_false_of_mem fun χ _ => ?_
      have hY0 : Y c χ γ γ' = 0 := by have := hY χ; omega
      simp [hY0]
    rw [this]; simp
  have hc := cheb_count (fun χ : Fin g → Fin K => Y c χ γ γ') (K ^ 2) U _ K (g * P) hV
  have e : ∀ χ : Fin g → Fin K, K * (K ^ 2 * Y c χ γ γ') = K ^ 3 * Y c χ γ γ' := fun χ => by ring
  simp only [e] at hc
  have hPpos : 0 < P := Nat.pos_of_mul_pos_left hpos
  have : (g * #{χ : Fin g → Fin K | K * U + g * P < K ^ 3 * Y c χ γ γ'}) * (g * P * P) ≤ (4 * K ^ 6 * K ^ g) * (g * P * P) := by
    calc _ = #{χ : Fin g → Fin K | K * U + g * P < K ^ 3 * Y c χ γ γ'} * (g * P) ^ 2 := by ring
      _ ≤ K ^ 2 * (4 * P * U * K ^ 4 * K ^ g) := hc
      _ = (4 * K ^ 6 * K ^ g * P) * U := by ring
      _ ≤ (4 * K ^ 6 * K ^ g * P) * (g * P) := Nat.mul_le_mul_left _ hU
      _ = (4 * K ^ 6 * K ^ g) * (g * P * P) := by ring
  exact Nat.le_of_mul_le_mul_right this (Nat.mul_pos hpos hPpos)

/-- «the fewer than K²/2 pairs of groups»: there are K(K − 1)/2 pairs γ < γ'. -/
theorem card_pairs_lt (hK : 1 ≤ K) : 2 * #{p : Fin K × Fin K | p.1 < p.2} < K ^ 2 := by
  have hswap : #{p : Fin K × Fin K | p.2 < p.1} = #{p : Fin K × Fin K | p.1 < p.2} := by
    refine card_bij (fun p _ => p.swap) ?_ ?_ ?_
    · intro p hp; simpa using hp
    · intro p _ q _ h; exact Prod.swap_injective h
    · intro p hp; exact ⟨p.swap, by simpa using hp, by simp⟩
  have hdiag : #{p : Fin K × Fin K | p.1 = p.2} = K := by
    have h := card_bij (s := (univ : Finset (Fin K))) (t := ({p : Fin K × Fin K | p.1 = p.2} : Finset (Fin K × Fin K))) (fun a _ => (a, a)) (by simp)
      (fun a _ b _ h => (Prod.mk.inj h).1) (fun p hp => ⟨p.1, mem_univ _, Prod.ext rfl (mem_filter.1 hp).2⟩)
    simpa using h.symm
  have hall : #{p : Fin K × Fin K | p.1 < p.2} + #{p : Fin K × Fin K | p.2 < p.1} + #{p : Fin K × Fin K | p.1 = p.2} = K ^ 2 := by
    rw [← card_union_of_disjoint, ← card_union_of_disjoint]
    · have : (({p : Fin K × Fin K | p.1 < p.2} : Finset (Fin K × Fin K)) ∪ ({p : Fin K × Fin K | p.2 < p.1} : Finset (Fin K × Fin K))) ∪ ({p : Fin K × Fin K | p.1 = p.2} : Finset (Fin K × Fin K)) = univ := by
        ext p
        simp only [mem_union, mem_filter, mem_univ, true_and, iff_true]
        rcases lt_trichotomy p.1 p.2 with h | h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
        · exact Or.inl (Or.inr h)
      rw [this]; simp [sq]
    · rw [disjoint_left]
      intro p hp hq
      simp only [mem_union, mem_filter, mem_univ, true_and] at hp hq
      rcases hp with h | h <;> exact absurd hq (by first | exact h.ne | exact h.ne')
    · rw [disjoint_left]
      intro p hp hq
      simp only [mem_filter, mem_univ, true_and] at hp hq
      exact absurd hq (not_lt.2 hp.le)
  omega

/-- «By a union bound over the fewer than K²/2 pairs of groups, some pair violates this bound with
probability less than» (K²/2)·(4K⁶/g), for every g: the union runs over the pairs γ < γ' only, since
Y_{γ,γ'} = Y_{γ',γ}. -/
theorem some_pair (hK : 1 ≤ K) {c : Fin g → Fin g → ℕ} (hs : ∀ a b, c a b = c b a) {P : ℕ} (hP : ∀ a, ∑ b ∈ univ.erase a, c a b ≤ P) :
    g * #{χ : Fin g → Fin K | ∃ γ γ', γ ≠ γ' ∧ K * (∑ a, ∑ b ∈ univ.erase a, c a b) + g * P < K ^ 3 * Y c χ γ γ'} < 2 * K ^ 8 * K ^ g := by
  have hsub : ({χ : Fin g → Fin K | ∃ γ γ', γ ≠ γ' ∧ K * (∑ a, ∑ b ∈ univ.erase a, c a b) + g * P < K ^ 3 * Y c χ γ γ'} : Finset (Fin g → Fin K)) ⊆
      ({p : Fin K × Fin K | p.1 < p.2} : Finset (Fin K × Fin K)).biUnion fun p => {χ : Fin g → Fin K | K * (∑ a, ∑ b ∈ univ.erase a, c a b) + g * P < K ^ 3 * Y c χ p.1 p.2} := by
    intro χ h
    simp only [mem_filter, mem_univ, true_and] at h
    obtain ⟨γ, γ', hne, hb⟩ := h
    simp only [mem_biUnion, mem_filter, mem_univ, true_and, Prod.exists]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨γ, γ', hlt, hb⟩
    · exact ⟨γ', γ, hgt, by rwa [Y_symm hs]⟩
  have hN : 0 < K ^ g := pow_pos hK g
  have h6 : 0 < K ^ 6 := pow_pos hK 6
  have hlt := card_pairs_lt hK
  have h1 : g * #{χ : Fin g → Fin K | ∃ γ γ', γ ≠ γ' ∧ K * (∑ a, ∑ b ∈ univ.erase a, c a b) + g * P < K ^ 3 * Y c χ γ γ'}
      ≤ #{p : Fin K × Fin K | p.1 < p.2} * (4 * K ^ 6 * K ^ g) := by
    calc _ ≤ g * ∑ p : Fin K × Fin K with p.1 < p.2, #{χ : Fin g → Fin K | K * (∑ a, ∑ b ∈ univ.erase a, c a b) + g * P < K ^ 3 * Y c χ p.1 p.2} :=
          Nat.mul_le_mul_left _ ((card_le_card hsub).trans card_biUnion_le)
      _ = ∑ p : Fin K × Fin K with p.1 < p.2, g * #{χ : Fin g → Fin K | K * (∑ a, ∑ b ∈ univ.erase a, c a b) + g * P < K ^ 3 * Y c χ p.1 p.2} := mul_sum _ _ _
      _ ≤ ∑ _p : Fin K × Fin K with _p.1 < _p.2, 4 * K ^ 6 * K ^ g := sum_le_sum fun p hp => cheb_Y hs hP (mem_filter.1 hp).2.ne
      _ = _ := by simp
  have h2 : #{p : Fin K × Fin K | p.1 < p.2} * (4 * K ^ 6 * K ^ g) < 2 * K ^ 8 * K ^ g := by
    calc #{p : Fin K × Fin K | p.1 < p.2} * (4 * K ^ 6 * K ^ g) = (2 * #{p : Fin K × Fin K | p.1 < p.2}) * (2 * K ^ 6 * K ^ g) := by ring
      _ < K ^ 2 * (2 * K ^ 6 * K ^ g) := Nat.mul_lt_mul_of_pos_right hlt (by positivity)
      _ = 2 * K ^ 8 * K ^ g := by ring
  exact lt_of_le_of_lt h1 h2

/-! ### The sizes of the groups -/

/-- «A group has mean size g/K». -/
theorem mean_size (γ : Fin K) : (∑ χ : Fin g → Fin K, #{a | χ a = γ}) * K = g * K ^ g := by
  have h := sum_Zs (ι := Fin g) γ
  simpa only [Fintype.card_fin, Zs_eq] using h

/-- «and variance at most g/K»: Σ_χ (|G_γ| − g/K)² ≤ (g/K)·K^g, multiplied by K². -/
theorem var_size (γ : Fin K) : ∑ χ : Fin g → Fin K, ((K : ℤ) * (#{a | χ a = γ} : ℕ) - (g : ℤ)) ^ 2 ≤ ((g * K * K ^ g : ℕ) : ℤ) := by
  have S2 := sum_Zs_sq (ι := Fin g) γ
  simp only [Fintype.card_fin, Zs_eq] at S2
  refine var_of_moments (fun χ : Fin g → Fin K => #{a | χ a = γ}) K g _ ?_ ?_
  · rw [mean_size]; simp [mul_comm]
  · simpa [mul_comm] using S2

/-- «so it exceeds 2g/K with probability at most K/g», for every g: Chebyshev with deviation g/K. -/
theorem cheb_size (γ : Fin K) : g * #{χ : Fin g → Fin K | 2 * g < K * #{a | χ a = γ}} ≤ K * K ^ g := by
  rcases Nat.eq_zero_or_pos g with h0 | hpos
  · subst h0; simp
  have hc := cheb_count (fun χ : Fin g → Fin K => #{a | χ a = γ}) K g _ 1 g (var_size γ)
  have e : ∀ χ : Fin g → Fin K, (1 * g + g < 1 * (K * #{a | χ a = γ})) ↔ (2 * g < K * #{a | χ a = γ}) := fun χ => by omega
  simp only [e] at hc
  have : (g * #{χ : Fin g → Fin K | 2 * g < K * #{a | χ a = γ}}) * g ≤ (K * K ^ g) * g := by
    calc _ = #{χ : Fin g → Fin K | 2 * g < K * #{a | χ a = γ}} * g ^ 2 := by ring
      _ ≤ 1 ^ 2 * (g * K * K ^ g) := hc
      _ = (K * K ^ g) * g := by ring
  exact Nat.le_of_mul_le_mul_right this hpos

/-- «by a union bound over the K groups, some group does so with probability at most K²/g», for
every g. -/
theorem some_group : g * #{χ : Fin g → Fin K | ∃ γ, 2 * g < K * #{a | χ a = γ}} ≤ K ^ 2 * K ^ g := by
  have hsub : ({χ : Fin g → Fin K | ∃ γ, 2 * g < K * #{a | χ a = γ}} : Finset (Fin g → Fin K)) ⊆
      (univ : Finset (Fin K)).biUnion fun γ => {χ : Fin g → Fin K | 2 * g < K * #{a | χ a = γ}} := by
    intro χ h
    simpa only [mem_biUnion, mem_filter, mem_univ, true_and] using h
  calc _ ≤ g * ∑ γ : Fin K, #{χ : Fin g → Fin K | 2 * g < K * #{a | χ a = γ}} := Nat.mul_le_mul_left _ ((card_le_card hsub).trans card_biUnion_le)
    _ = ∑ γ : Fin K, g * #{χ : Fin g → Fin K | 2 * g < K * #{a | χ a = γ}} := mul_sum _ _ _
    _ ≤ ∑ _γ : Fin K, K * K ^ g := sum_le_sum fun γ _ => cheb_size γ
    _ = K ^ 2 * K ^ g := by simp; ring

/-! ### g = 3K⁸ -/

/-- «By a union bound over these two events, the grouping fails to be good with probability less
than 1, so a good grouping exists.» From «less than 2/3» and «less than 1/3». -/
theorem exists_good_of {c : Fin g → Fin g → ℕ} {P : ℕ}
    (h1 : 3 * #{χ : Fin g → Fin K | ∃ γ γ', γ ≠ γ' ∧ K * (∑ a, ∑ b ∈ univ.erase a, c a b) + g * P < K ^ 3 * Y c χ γ γ'} < 2 * K ^ g)
    (h2 : 3 * #{χ : Fin g → Fin K | ∃ γ, 2 * g < K * #{a | χ a = γ}} < K ^ g) : ∃ χ : Fin g → Fin K, Good c P χ := by
  by_contra hcon
  have hcov : (univ : Finset (Fin g → Fin K)) ⊆
      ({χ : Fin g → Fin K | ∃ γ γ', γ ≠ γ' ∧ K * (∑ a, ∑ b ∈ univ.erase a, c a b) + g * P < K ^ 3 * Y c χ γ γ'} : Finset (Fin g → Fin K)) ∪
        ({χ : Fin g → Fin K | ∃ γ, 2 * g < K * #{a | χ a = γ}} : Finset (Fin g → Fin K)) := by
    intro χ _
    by_contra hχ
    simp only [mem_union, mem_filter, mem_univ, true_and, not_or, not_exists, not_and, not_lt] at hχ
    exact hcon ⟨χ, ⟨hχ.2, hχ.1⟩⟩
  have h3 := (card_le_card hcov).trans (card_union_le _ _)
  have h4 : #(univ : Finset (Fin g → Fin K)) = K ^ g := by simp
  omega

/-- **«A good grouping exists»**: the steps of the paragraph at g = 3K⁸, with the numbers 4/(3K²),
2/3, K/g, 1/3 of the text. Same as in the paper, but for probabilities written as counts over the
K^g groupings. -/
theorem groupingFacts : GroupingFacts := by
  have pairs : ∀ (K P : ℕ) (c : Fin (3 * K ^ 8) → Fin (3 * K ^ 8) → ℕ), 2 ≤ K → (∀ a b, c a b = c b a) → (∀ a, ∑ b ∈ univ.erase a, c a b ≤ P) →
      3 * #{χ : Fin (3 * K ^ 8) → Fin K | ∃ γ γ', γ ≠ γ' ∧ K * (∑ a, ∑ b ∈ univ.erase a, c a b) + 3 * K ^ 8 * P < K ^ 3 * Y c χ γ γ'} < 2 * K ^ (3 * K ^ 8) := by
    intro K P c hK hs hP
    have h := some_pair (K := K) (by omega) hs hP
    have h8 : 0 < K ^ 8 := pow_pos (by omega) 8
    refine Nat.lt_of_mul_lt_mul_left (a := K ^ 8) ?_
    calc _ = 3 * K ^ 8 * #{χ : Fin (3 * K ^ 8) → Fin K | ∃ γ γ', γ ≠ γ' ∧ K * (∑ a, ∑ b ∈ univ.erase a, c a b) + 3 * K ^ 8 * P < K ^ 3 * Y c χ γ γ'} := by ring
      _ < 2 * K ^ 8 * K ^ (3 * K ^ 8) := h
      _ = _ := by ring
  have groups : ∀ K : ℕ, 2 ≤ K → 3 * #{χ : Fin (3 * K ^ 8) → Fin K | ∃ γ, 2 * (3 * K ^ 8) < K * #{a | χ a = γ}} < K ^ (3 * K ^ 8) := by
    intro K hK
    have h := some_group (g := 3 * K ^ 8) (K := K)
    have h2 : 0 < K ^ 2 := pow_pos (by omega) 2
    have hN : 0 < K ^ (3 * K ^ 8) := pow_pos (by omega) _
    have h6 : 1 < K ^ 6 := Nat.one_lt_pow (by omega) (by omega)
    -- K²/g = 1/(3K⁶) < 1/3
    have h' : K ^ 6 * (3 * #{χ : Fin (3 * K ^ 8) → Fin K | ∃ γ, 2 * (3 * K ^ 8) < K * #{a | χ a = γ}}) ≤ K ^ (3 * K ^ 8) := by
      refine Nat.le_of_mul_le_mul_left ?_ h2
      calc _ = 3 * K ^ 8 * #{χ : Fin (3 * K ^ 8) → Fin K | ∃ γ, 2 * (3 * K ^ 8) < K * #{a | χ a = γ}} := by ring
        _ ≤ _ := h
    rcases Nat.eq_zero_or_pos (3 * #{χ : Fin (3 * K ^ 8) → Fin K | ∃ γ, 2 * (3 * K ^ 8) < K * #{a | χ a = γ}}) with h0 | hp
    · rw [h0]; exact hN
    · exact lt_of_lt_of_le (by nlinarith) h'
  refine ⟨?_, pairs, fun K _ γ => cheb_size γ, groups, fun K P c hK hs hP => exists_good_of (pairs K P c hK hs hP) (groups K hK)⟩
  intro K P c hK hs hP γ γ' hne
  have h := cheb_Y hs hP hne
  have h6 : 0 < K ^ 6 := pow_pos (by omega) 6
  -- 4K⁶/g = 4/(3K²)
  refine Nat.le_of_mul_le_mul_left ?_ h6
  calc _ = 3 * K ^ 8 * #{χ : Fin (3 * K ^ 8) → Fin K | K * (∑ a, ∑ b ∈ univ.erase a, c a b) + 3 * K ^ 8 * P < K ^ 3 * Y c χ γ γ'} := by ring
    _ ≤ 4 * K ^ 6 * K ^ (3 * K ^ 8) := h
    _ = _ := by ring

end Eight.SecNetworks
