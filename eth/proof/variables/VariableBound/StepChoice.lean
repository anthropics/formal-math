/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import AppVariablesStatement
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.List
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Appendix D, Step 2 (finding the checks): the mathematics

Proves `AppVariables.StepChoice`, for an abstract family Γ_u, u ∈ Ω, with the properties (a), (b), (c)
of Lemma 13 (`AppVariables.IsFamily`). The argument is the one of the text:

* appending Γ_u multiplies the term of ξ in X(𝓛) by [ |Γ_u ∩ V(ξ)| even ]; a nonzero term has |V(ξ)| >
  n̄, so by (c) the average of X(𝓛, Γ_u) is at most (3/4)·X(𝓛) (`avgX`);
* by (b) the average of 2^[E ∈ Γ_u] is at most 1 + p (`avgCol`);
* so, for a list of fewer than r̄ checks, the average of Υ(𝓛, Γ_u) is at most Υ(𝓛) (`avgUps`), and
  so is the minimum (`minUps`);
* for the empty list both terms of Υ are at most 1 (`ups_nil`);
* Υ(𝓛) ≤ 2 gives X(𝓛) ≤ (3/4)^r·2^β (`x_of_ups`) and load(E) ≤ t̄ + 1 (`load_of_ups`); a list with
  X(𝓛) > 0 and this bound has fewer than r̄ checks (`lt_rb`);
* hence, by induction along the algorithm, every reached list has at most r̄ checks and Υ ≤ 2
  (`reached`); if Ω is not empty, the algorithm can go on while X(𝓛) > 0 (`progress`).

The text defines Υ for lists of at most r̄ checks and bounds r after Υ; here the two bounds are
proved together, because the step from 𝓛 to (𝓛, Γ_u) uses r < r̄. The condition m > n̄ of the text
and the
minimality of r̄ and t̄ are not used. -/

public section

namespace VariableBound.StepChoice

open AppVariables Finset

variable {X E ι : Type} [Fintype X] [Fintype E] [DecidableEq E]

/-! ### The factors [q even] and the sum X(𝓛) -/

/-- 0 ≤ [q even]. -/
theorem ev_nonneg (q : ℕ) : 0 ≤ ParityChecks.ev q := by
  unfold ParityChecks.ev; split <;> norm_num

omit [Fintype X] [Fintype E] in
/-- 0 ≤ ∏_j [ |V_j(ξ)| even ]. -/
theorem allEven_nonneg (V : X → Finset E) (L : List (Finset E)) (ξ : X) : 0 ≤ allEven V L ξ := by
  unfold allEven
  refine List.prod_nonneg fun a ha => ?_
  obtain ⟨Λ, -, rfl⟩ := List.mem_map.1 ha
  exact ev_nonneg _

omit [Fintype X] [Fintype E] in
/-- Appending the check Γ multiplies the product of ξ by [ |Γ ∩ V(ξ)| even ]. -/
theorem allEven_append (V : X → Finset E) (L : List (Finset E)) (Γ : Finset E) (ξ : X) :
    allEven V (L ++ [Γ]) ξ = allEven V L ξ * ParityChecks.ev #(Γ ∩ V ξ) := by
  simp [allEven]

omit [Fintype E] in
/-- 0 ≤ X(𝓛). -/
theorem Xsum_nonneg (V : X → Finset E) (nb : ℕ) (L : List (Finset E)) : 0 ≤ Xsum V nb L :=
  sum_nonneg fun ξ _ => mul_nonneg (by positivity) (allEven_nonneg V L ξ)

/-- For the empty list, X ≤ 2^n·C(m, n̄+1), if there are at most 2^n assignments. -/
theorem Xsum_nil_le (V : X → Finset E) (nb n : ℕ) (hX : Fintype.card X ≤ 2 ^ n) :
    Xsum V nb [] ≤ 2 ^ n * ((Fintype.card E).choose (nb + 1) : ℤ) := by
  have h : ∀ ξ ∈ (univ : Finset X), ((#(V ξ)).choose (nb + 1) : ℤ) * allEven V [] ξ ≤ ((Fintype.card E).choose (nb + 1) : ℤ) := by
    intro ξ _
    simp only [allEven, List.map_nil, List.prod_nil, mul_one]
    exact_mod_cast Nat.choose_le_choose _ (card_le_univ _)
  calc Xsum V nb [] ≤ #(univ : Finset X) • ((Fintype.card E).choose (nb + 1) : ℤ) := sum_le_card_nsmul _ _ _ h
    _ = (Fintype.card X : ℤ) * ((Fintype.card E).choose (nb + 1) : ℤ) := by rw [card_univ, nsmul_eq_mul]
    _ ≤ 2 ^ n * ((Fintype.card E).choose (nb + 1) : ℤ) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact_mod_cast hX

/-! ### The two averages -/

/-- For a family as in Lemma 13 with v = n̄, by its part (c): for a set W of more than n̄ clauses, [ |Γ_u
∩ W| even ] is 1 for at most three quarters of the u ∈ Ω. -/
theorem sum_ev_le {nb : ℕ} {Ω : Finset ι} {Γ : ι → Finset E} (hF : IsFamily nb Ω Γ) (W : Finset E) (hW : nb < #W) :
    4 * ∑ u ∈ Ω, ParityChecks.ev #(Γ u ∩ W) ≤ 3 * (#Ω : ℤ) := by
  have h1 : ∑ u ∈ Ω, ParityChecks.ev #(Γ u ∩ W) = (#{u ∈ Ω | Even #(Γ u ∩ W)} : ℤ) := by
    unfold ParityChecks.ev; rw [sum_boole]
  have h2 : #{u ∈ Ω | Even #(Γ u ∩ W)} + #{u ∈ Ω | Odd #(Γ u ∩ W)} = #Ω := by
    simp only [← Nat.not_even_iff_odd]
    exact card_filter_add_card_filter_not _
  have h3 := hF.c W hW
  rw [h1]
  have : 4 * #{u ∈ Ω | Even #(Γ u ∩ W)} ≤ 3 * #Ω := by omega
  exact_mod_cast this

/-- Step 2, «the average of X(𝓛, Γ_u) over u ∈ Ω is at most (3/4)·X(𝓛)», for a family as in Lemma 13
with v = n̄. -/
theorem avgX (V : X → Finset E) (nb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) (L : List (Finset E)) (hF : IsFamily nb Ω Γ) :
    4 * ∑ u ∈ Ω, Xsum V nb (L ++ [Γ u]) ≤ 3 * #Ω * Xsum V nb L := by
  calc 4 * ∑ u ∈ Ω, Xsum V nb (L ++ [Γ u])
      = ∑ ξ, ((#(V ξ)).choose (nb + 1) : ℤ) * allEven V L ξ * (4 * ∑ u ∈ Ω, ParityChecks.ev #(Γ u ∩ V ξ)) := by
        simp only [Xsum, allEven_append]
        rw [sum_comm, mul_sum]
        refine sum_congr rfl fun ξ _ => ?_
        rw [mul_sum, mul_sum, mul_sum]
        exact sum_congr rfl fun u _ => by ring
    _ ≤ ∑ ξ, ((#(V ξ)).choose (nb + 1) : ℤ) * allEven V L ξ * (3 * (#Ω : ℤ)) := by
        refine sum_le_sum fun ξ _ => ?_
        by_cases h : nb < #(V ξ)
        · exact mul_le_mul_of_nonneg_left (sum_ev_le hF _ h) (mul_nonneg (by positivity) (allEven_nonneg V L ξ))
        · rw [Nat.choose_eq_zero_of_lt (by omega)]; simp
    _ = 3 * #Ω * Xsum V nb L := by
        rw [Xsum, mul_sum]
        exact sum_congr rfl fun ξ _ => by ring

/-- 0 ≤ p. -/
theorem pp_nonneg (nb : ℕ) : 0 ≤ pp nb := by unfold pp; positivity

/-- Step 2, «the average of 2^[E ∈ Γ_u] is at most 1 + p», for a family as in Lemma 13 with v = n̄ ≥ 1. -/
theorem avgCol (nb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) (e : E) (hnb : 1 ≤ nb) (hF : IsFamily nb Ω Γ) :
    ∑ u ∈ Ω, (2 : ℚ) ^ (if e ∈ Γ u then 1 else 0) ≤ (1 + pp nb) * #Ω := by
  have h1 : ∑ u ∈ Ω, (2 : ℚ) ^ (if e ∈ Γ u then 1 else 0) = #Ω + #{u ∈ Ω | e ∈ Γ u} := by
    rw [← sum_boole, card_eq_sum_ones, Nat.cast_sum, ← sum_add_distrib]
    refine sum_congr rfl fun u _ => ?_
    split <;> norm_num
  have h2 : (15 : ℚ) * nb * #{u ∈ Ω | e ∈ Γ u} ≤ 16 * #Ω := by exact_mod_cast hF.b e
  have h3 : (0 : ℚ) < 15 * nb := by
    have : (0 : ℚ) < nb := by exact_mod_cast hnb
    positivity
  have h4 : (#{u ∈ Ω | e ∈ Γ u} : ℚ) ≤ pp nb * #Ω := by
    unfold pp
    rw [div_mul_eq_mul_div, le_div_iff₀ h3]
    linarith
  rw [h1]; linarith

/-! ### The potential Υ -/

omit [Fintype E] in
/-- load(E) for the list (𝓛, Γ) is load(E) for 𝓛 plus [E ∈ Γ]. -/
theorem load_append (L : List (Finset E)) (Γ : Finset E) (e : E) : load (L ++ [Γ]) e = load L e + if e ∈ Γ then 1 else 0 := by
  unfold load
  rw [List.filter_append, List.length_append]
  by_cases h : e ∈ Γ <;> simp [h]

/-- Step 2, «the average of Υ(𝓛, Γ_u) is at most Υ(𝓛)», for a list of fewer than r̄ checks and a
family as in Lemma 13 with v = n̄ ≥ 1. -/
theorem avgUps (V : X → Finset E) (nb β rb tb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) (L : List (Finset E)) (hnb : 1 ≤ nb) (hF : IsFamily nb Ω Γ)
    (hr : L.length < rb) : ∑ u ∈ Ω, Ups V nb β rb tb (L ++ [Γ u]) ≤ #Ω * Ups V nb β rb tb L := by
  have h1 : (4 : ℚ) * ∑ u ∈ Ω, (Xsum V nb (L ++ [Γ u]) : ℚ) ≤ 3 * #Ω * (Xsum V nb L : ℚ) := by exact_mod_cast avgX V nb Ω Γ L hF
  have h2 : ∀ e, ∑ u ∈ Ω, (2 : ℚ) ^ load (L ++ [Γ u]) e ≤ 2 ^ load L e * ((1 + pp nb) * #Ω) := by
    intro e
    simp only [load_append, pow_add]
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left (avgCol nb Ω Γ e hnb hF) (by positivity)
  have hp := pp_nonneg nb
  obtain ⟨d, hd⟩ : ∃ d, rb - L.length = d + 1 := ⟨rb - L.length - 1, by omega⟩
  have hd' : rb - (L.length + 1) = d := by omega
  unfold Ups
  simp only [List.length_append, List.length_singleton, hd, hd']
  rw [sum_add_distrib, ← sum_div, ← mul_sum, ← mul_sum, sum_comm, mul_add]
  refine add_le_add ?_ ?_
  · calc (4 / 3 : ℚ) ^ (L.length + 1) * (∑ u ∈ Ω, (Xsum V nb (L ++ [Γ u]) : ℚ)) / 2 ^ (β - 1)
        = (4 / 3 : ℚ) ^ L.length / 2 ^ (β - 1) * (4 * ∑ u ∈ Ω, (Xsum V nb (L ++ [Γ u]) : ℚ)) / 3 := by ring
      _ ≤ (4 / 3 : ℚ) ^ L.length / 2 ^ (β - 1) * (3 * #Ω * (Xsum V nb L : ℚ)) / 3 := by gcongr
      _ = #Ω * ((4 / 3 : ℚ) ^ L.length * (Xsum V nb L : ℚ) / 2 ^ (β - 1)) := by ring
  · calc (1 + pp nb) ^ d * (1 / 2 ^ tb) * ∑ e : E, ∑ u ∈ Ω, (2 : ℚ) ^ load (L ++ [Γ u]) e
        ≤ (1 + pp nb) ^ d * (1 / 2 ^ tb) * ∑ e : E, (2 : ℚ) ^ load L e * ((1 + pp nb) * #Ω) := by
          gcongr with e _
          exact h2 e
      _ = #Ω * ((1 + pp nb) ^ (d + 1) * (1 / 2 ^ tb) * ∑ e : E, (2 : ℚ) ^ load L e) := by
          rw [← sum_mul]; ring

/-- Step 2, «and so is the minimum»: under the hypotheses of `avgUps`, a list (𝓛, Γ_u), u ∈ Ω, with
the smallest Υ has Υ(𝓛, Γ_u) ≤ Υ(𝓛). -/
theorem minUps (V : X → Finset E) (nb β rb tb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) (L : List (Finset E)) (hnb : 1 ≤ nb) (hF : IsFamily nb Ω Γ)
    (hr : L.length < rb) (u : ι) (hu : u ∈ Ω) (hmin : ∀ u' ∈ Ω, Ups V nb β rb tb (L ++ [Γ u]) ≤ Ups V nb β rb tb (L ++ [Γ u'])) :
    Ups V nb β rb tb (L ++ [Γ u]) ≤ Ups V nb β rb tb L := by
  have h0 : (0 : ℚ) < #Ω := by exact_mod_cast card_pos.2 ⟨u, hu⟩
  have h1 : #Ω • Ups V nb β rb tb (L ++ [Γ u]) ≤ ∑ u' ∈ Ω, Ups V nb β rb tb (L ++ [Γ u']) := card_nsmul_le_sum _ _ _ hmin
  rw [nsmul_eq_mul] at h1
  exact le_of_mul_le_mul_left (h1.trans (avgUps V nb β rb tb Ω Γ L hnb hF hr)) h0

omit [Fintype E] in
/-- The first term of Υ is not negative. -/
theorem first_nonneg (V : X → Finset E) (nb β : ℕ) (L : List (Finset E)) : (0 : ℚ) ≤ (4 / 3) ^ L.length * (Xsum V nb L : ℚ) / 2 ^ (β - 1) := by
  have : (0 : ℚ) ≤ (Xsum V nb L : ℚ) := by exact_mod_cast Xsum_nonneg V nb L
  positivity

/-- The second term of Υ is not negative. -/
theorem second_nonneg (nb rb tb : ℕ) (L : List (Finset E)) : 0 ≤ (1 + pp nb) ^ (rb - L.length) * (1 / 2 ^ tb) * ∑ e : E, (2 : ℚ) ^ load L e := by
  have := pp_nonneg nb
  positivity

/-- Step 2, «for the empty list both terms are at most 1, by X ≤ 2^(β−1) and the choice of t̄»: Υ ≤
2 for the empty list, if there are at most 2^n assignments, β is the β of the text and
m·(1+p)^r̄ ≤ 2^t̄. -/
theorem ups_nil (V : X → Finset E) (n nb rb tb : ℕ) (hX : Fintype.card X ≤ 2 ^ n) (ht : (Fintype.card E : ℚ) * (1 + pp nb) ^ rb ≤ 2 ^ tb) :
    Ups V nb (beta n (Fintype.card E) nb) rb tb [] ≤ 2 := by
  have h1 : Xsum V nb [] ≤ 2 ^ (beta n (Fintype.card E) nb - 1) := by
    refine (Xsum_nil_le V nb n hX).trans ?_
    have : beta n (Fintype.card E) nb - 1 = n + Nat.clog 2 ((Fintype.card E).choose (nb + 1)) := by unfold beta; omega
    rw [this, pow_add]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact_mod_cast Nat.le_pow_clog (by norm_num) _
  have h1' : (Xsum V nb [] : ℚ) ≤ 2 ^ (beta n (Fintype.card E) nb - 1) := by exact_mod_cast h1
  unfold Ups
  have e1 : (4 / 3 : ℚ) ^ ([] : List (Finset E)).length * (Xsum V nb [] : ℚ) / 2 ^ (beta n (Fintype.card E) nb - 1) ≤ 1 := by
    rw [List.length_nil, pow_zero, one_mul, div_le_one (by positivity)]
    exact h1'
  have e2 : (1 + pp nb) ^ (rb - ([] : List (Finset E)).length) * (1 / 2 ^ tb) * ∑ e : E, (2 : ℚ) ^ load [] e ≤ 1 := by
    have : ∑ e : E, (2 : ℚ) ^ load [] e = Fintype.card E := by simp [load]
    rw [this, List.length_nil, Nat.sub_zero]
    calc (1 + pp nb) ^ rb * (1 / 2 ^ tb) * (Fintype.card E : ℚ) = (Fintype.card E : ℚ) * (1 + pp nb) ^ rb / 2 ^ tb := by ring
      _ ≤ 1 := by rw [div_le_one (by positivity)]; exact ht
  linarith

/-- Step 2, «hence X(𝓛) ≤ (3/4)^r·2^β»: from Υ(𝓛) ≤ 2 and β ≥ 1. -/
theorem x_of_ups (V : X → Finset E) (nb β rb tb : ℕ) (L : List (Finset E)) (hβ : 1 ≤ β) (h : Ups V nb β rb tb L ≤ 2) :
    4 ^ L.length * Xsum V nb L ≤ 3 ^ L.length * 2 ^ β := by
  have h1 : (4 / 3 : ℚ) ^ L.length * (Xsum V nb L : ℚ) / 2 ^ (β - 1) ≤ 2 := by
    have := second_nonneg nb rb tb L
    unfold Ups at h
    linarith
  have h2 : (2 : ℚ) ^ β = 2 * 2 ^ (β - 1) := by
    obtain ⟨b, rfl⟩ : ∃ b, β = b + 1 := ⟨β - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]; ring
  have h3 : (4 : ℚ) ^ L.length * (Xsum V nb L : ℚ) ≤ 3 ^ L.length * 2 ^ β := by
    rw [div_le_iff₀ (by positivity), div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at h1
    rw [h2]; linarith
  exact_mod_cast h3

omit [Fintype E] in
/-- A list with X(𝓛) > 0, at most r̄ checks and X(𝓛) ≤ (3/4)^r·2^β has fewer than r̄ checks, because
3^r̄·2^β < 4^r̄. -/
theorem lt_rb (V : X → Finset E) (nb β rb : ℕ) (L : List (Finset E)) (hrb : 3 ^ rb * 2 ^ β < 4 ^ rb) (hl : L.length ≤ rb) (hpos : 0 < Xsum V nb L)
    (h : 4 ^ L.length * Xsum V nb L ≤ 3 ^ L.length * 2 ^ β) : L.length < rb := by
  rcases hl.lt_or_eq with h' | h'
  · exact h'
  · exfalso
    rw [h'] at h
    have h1 : (3 : ℤ) ^ rb * 2 ^ β < 4 ^ rb := by exact_mod_cast hrb
    have h2 : (4 : ℤ) ^ rb * 1 ≤ 4 ^ rb * Xsum V nb L := mul_le_mul_of_nonneg_left (by omega) (by positivity)
    linarith

/-- Step 2, «also 2^(load(E)−t̄) ≤ 2 for every clause E»: from Υ(𝓛) ≤ 2, load(E) ≤ t̄ + 1. -/
theorem load_of_ups (V : X → Finset E) (nb β rb tb : ℕ) (L : List (Finset E)) (h : Ups V nb β rb tb L ≤ 2) (e : E) : load L e ≤ tb + 1 := by
  have h1 : (1 + pp nb) ^ (rb - L.length) * (1 / 2 ^ tb) * ∑ e : E, (2 : ℚ) ^ load L e ≤ 2 := by
    have := first_nonneg V nb β L
    unfold Ups at h
    linarith
  have h2 : (2 : ℚ) ^ load L e ≤ ∑ e : E, (2 : ℚ) ^ load L e := single_le_sum (f := fun e => (2 : ℚ) ^ load L e) (fun _ _ => by positivity) (mem_univ e)
  have h3 : (1 : ℚ) ≤ (1 + pp nb) ^ (rb - L.length) := one_le_pow₀ (by have := pp_nonneg nb; linarith)
  have h4 : 1 * (1 / 2 ^ tb) * (2 : ℚ) ^ load L e ≤ 2 := le_trans (by gcongr) h1
  have h5 : (2 : ℚ) ^ load L e ≤ 2 ^ (tb + 1) := by
    rw [one_mul, one_div, inv_mul_le_iff₀ (by positivity)] at h4
    rw [pow_succ]; linarith
  exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℚ) < 2)).1 h5

/-! ### Along the algorithm -/

/-- 1 ≤ β. -/
theorem one_le_beta (n m nb : ℕ) : 1 ≤ beta n m nb := by unfold beta; omega

/-- Step 2, «every list that is reached has Υ(𝓛) ≤ 2», together with r ≤ r̄. Hypotheses: at most 2^n
assignments, n̄ ≥ 1, β, r̄, t̄ as in the text, a family as in Lemma 13 with v = n̄. -/
theorem reached (V : X → Finset E) (n nb rb tb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) (L : List (Finset E)) (hX : Fintype.card X ≤ 2 ^ n) (hnb : 1 ≤ nb)
    (hrb : IsRb (beta n (Fintype.card E) nb) rb) (htb : IsTb (Fintype.card E) nb rb tb) (hF : IsFamily nb Ω Γ)
    (hL : Reached V nb (beta n (Fintype.card E) nb) rb tb Ω Γ L) : L.length ≤ rb ∧ Ups V nb (beta n (Fintype.card E) nb) rb tb L ≤ 2 := by
  induction hL with
  | nil => exact ⟨Nat.zero_le _, ups_nil V n nb rb tb hX htb.1⟩
  | step L u _ hpos hu hmin ih =>
    have hlt := lt_rb V nb _ rb L hrb.1 ih.1 hpos (x_of_ups V nb _ rb tb L (one_le_beta _ _ _) ih.2)
    refine ⟨by rw [List.length_append, List.length_singleton]; omega, ?_⟩
    exact (minUps V nb _ rb tb Ω Γ L hnb hF hlt u hu hmin).trans ih.2

/-- Every check of a reached list is one of the Γ_u, u ∈ Ω. -/
theorem reached_mem (V : X → Finset E) (nb β rb tb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) (L : List (Finset E)) (hL : Reached V nb β rb tb Ω Γ L) :
    ∀ Λ ∈ L, ∃ u ∈ Ω, Λ = Γ u := by
  induction hL with
  | nil => intro Λ h; simp at h
  | step L u _ _ hu _ ih =>
    intro Λ h
    rcases List.mem_append.1 h with h | h
    · exact ih Λ h
    · exact ⟨u, hu, List.mem_singleton.1 h⟩

/-- If 𝓛 is reached, X(𝓛) > 0 and Ω is not empty, the algorithm can go on: among the lists (𝓛, Γ_u),
u ∈ Ω, one has the smallest Υ, and it is reached. -/
theorem progress (V : X → Finset E) (nb β rb tb : ℕ) (Ω : Finset ι) (Γ : ι → Finset E) (L : List (Finset E)) (hΩ : Ω.Nonempty)
    (hL : Reached V nb β rb tb Ω Γ L) (hpos : 0 < Xsum V nb L) : ∃ u ∈ Ω, Reached V nb β rb tb Ω Γ (L ++ [Γ u]) := by
  obtain ⟨u, hu, hmin⟩ := exists_min_image Ω (fun u => Ups V nb β rb tb (L ++ [Γ u])) hΩ
  exact ⟨u, hu, Reached.step L u hL hpos hu hmin⟩

end VariableBound.StepChoice

namespace VariableBound

open AppVariables Finset

/-- Step 2 of Appendix D (finding the checks): the averages of X, 2^[E ∈ Γ_u] and Υ, r ≤ r̄ and Υ ≤
2 on reached lists, X(𝓛) ≤ (3/4)^r·2^β, the loop's progress and end, and the bounds on r, |Λ_j|,
load(E). -/
theorem stepChoice : AppVariables.StepChoice where
  avgX := fun _ _ _ _ _ _ V nb Ω Γ L hF => StepChoice.avgX V nb Ω Γ L hF
  avgCol := fun _ _ _ _ nb Ω Γ e hnb hF => StepChoice.avgCol nb Ω Γ e hnb hF
  avgUps := fun _ _ _ _ _ _ V nb β rb tb Ω Γ L hnb hF hr => StepChoice.avgUps V nb β rb tb Ω Γ L hnb hF hr
  ups_le := fun _ _ _ _ _ _ V n nb rb tb Ω Γ L hX hnb hrb htb hF hL => StepChoice.reached V n nb rb tb Ω Γ L hX hnb hrb htb hF hL
  x_le := fun _ _ _ _ _ _ V n nb rb tb Ω Γ L hX hnb hrb htb hF hL =>
    StepChoice.x_of_ups V nb _ rb tb L (StepChoice.one_le_beta _ _ _) (StepChoice.reached V n nb rb tb Ω Γ L hX hnb hrb htb hF hL).2
  progress := fun _ _ _ _ _ _ V nb β rb tb Ω Γ L hΩ hL hpos => StepChoice.progress V nb β rb tb Ω Γ L hΩ hL hpos
  ends := by
    intro X E ι _ _ _ V n nb rb tb Ω Γ L hX hnb hrb htb hF hL hlen
    have h := StepChoice.reached V n nb rb tb Ω Γ L hX hnb hrb htb hF hL
    by_contra hne
    have hpos : 0 < Xsum V nb L := lt_of_le_of_ne (StepChoice.Xsum_nonneg V nb L) (Ne.symm hne)
    have := StepChoice.lt_rb V nb _ rb L hrb.1 h.1 hpos (StepChoice.x_of_ups V nb _ rb tb L (StepChoice.one_le_beta _ _ _) h.2)
    omega
  structure_ := by
    intro X E ι _ _ _ V n nb rb tb Ω Γ L L' hX hnb hrb htb hF hL hL'
    have h := StepChoice.reached V n nb rb tb Ω Γ L hX hnb hrb htb hF hL
    have hm := StepChoice.reached_mem V nb _ rb tb Ω Γ L hL
    have hc := StepChoice.load_of_ups V nb _ rb tb L h.2
    have ha : ∀ Λ ∈ L, nb * #Λ ≤ 16 * Fintype.card E := by
      intro Λ hΛ
      obtain ⟨u, hu, rfl⟩ := hm Λ hΛ
      exact hF.a u hu
    rcases hL' with rfl | ⟨hpos, u, hu, rfl⟩
    · exact ⟨h.1, ha, fun e => (hc e).trans (by omega)⟩
    · have hlt := StepChoice.lt_rb V nb _ rb L hrb.1 h.1 hpos (StepChoice.x_of_ups V nb _ rb tb L (StepChoice.one_le_beta _ _ _) h.2)
      refine ⟨by rw [List.length_append, List.length_singleton]; omega, ?_, ?_⟩
      · intro Λ hΛ
        rcases List.mem_append.1 hΛ with hΛ | hΛ
        · exact ha Λ hΛ
        · rw [List.mem_singleton.1 hΛ]; exact hF.a u hu
      · intro e
        rw [StepChoice.load_append]
        have := hc e
        split <;> omega

end VariableBound
