/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec2.Lemma7_8
public import ThreeSumApsp.Util.Counting
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Ring.Rat
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Section 2.4.3, first half: the orders of the leaves and equation (5)

A leaf that contributes to an output string with inner set `Q` is free at the `m` levels of `Q` and
fixed at the other levels.  Its order is `m` minus the number of levels at which it chooses `P₀`.

* One level.  A term contributes to `z` exactly if `z = z₀` or the term is the private term of `z`
  (`Term.contributes_iff`), so a leaf contributing to a string chooses `P₀` only at levels of the
  inner set (`P0Levels_subset`).  The numbers of terms of each kind that contribute to a variable,
  and of variables of each kind to which a term contributes, are read off the ten terms.
* Counts.  `10^m` leaves contribute to a string: ten terms for each level of `Q`
  (`card_filter_contributes`).  The other counts sort strings by the set of levels at which they
  have a letter of a given kind (`Finset.card_pi_places_card`, `Finset.card_places_card`): `α_d` of
  the leaves contributing to a string have order `d` (`sec2_card_contributing_of_order`), the whole
  tree has `β_d` leaves of order `d` (`card_filter_order_eq`), with `β₀ = M` (`beta_zero_eq_M`), and
  a leaf of order `d` contributes to `binom(L-m+d, d)` strings (`sec2_card_outStr_of_leaf`). Figure
  6 shows these numbers for `L = 6` and `m = 2` (`figure_6`).
* Equation (5): the quotient `β_d / β_{d-1}` comes from the recurrence of the binomial coefficients
  (`Equation5.ratio_nat`, `eq_5_ratio`); for `L = 19m` it is less than `1/2` (`eq_5_bound`); so
  `β_d ≤ 2^{-d} M` by induction on `d` (`eq_5`).
-/

public section

open Finset

namespace ThreeSumApsp

/-! ### One level: which terms contribute to which variables -/

/-- The private term of `z` is `P₀` exactly if `z = z₀`. -/
theorem OutVar.privateTerm_eq_P0_iff (z : OutVar) : z.privateTerm = Term.P0 ↔ z.IsInner := by
  cases z <;> simp [OutVar.IsInner, OutVar.privateTerm]

/-- One term is `P₀`. -/
private theorem card_term_P0 : (univ.filter fun lam : Term => lam = Term.P0).card = 1 := by decide

/-- Nine terms are different from `P₀`. -/
private theorem card_term_ne_P0 : (univ.filter fun lam : Term => ¬ lam = Term.P0).card = 9 := by
  decide

/-- Among the terms contributing to `z`, the number of those equal to `P₀`: one if `z = z₀`, none if
`z = z_ij`. -/
private theorem card_contributing_P0 (z : OutVar) :
    ((univ.filter fun lam : Term => lam.Contributes z).filter fun lam => lam = Term.P0).card
      = if z.IsInner then 1 else 0 := by
  decide +revert

/-- Among the terms contributing to `z`, the number of those different from `P₀`: nine if `z = z₀`,
one if `z = z_ij`. -/
private theorem card_contributing_ne_P0 (z : OutVar) :
    ((univ.filter fun lam : Term => lam.Contributes z).filter fun lam => ¬ lam = Term.P0).card
      = if z.IsInner then 9 else 1 := by
  decide +revert

/-- The number of terms contributing to `z`: ten if `z = z₀`, one if `z = z_ij`. -/
private theorem card_contributing_term (z : OutVar) :
    (univ.filter fun lam : Term => lam.Contributes z).card = if z.IsInner then 10 else 1 := by
  decide +revert

/-- Among the output variables to which `lam` contributes, exactly one is inner. -/
private theorem card_contributed_inner (lam : Term) :
    ((univ.filter fun z : OutVar => lam.Contributes z).filter fun z => z.IsInner).card = 1 := by
  decide +revert

/-- Among the output variables to which `lam` contributes, the number of outer ones: none if
`lam = P₀`, one if `lam = P_ij`. -/
private theorem card_contributed_outer (lam : Term) :
    ((univ.filter fun z : OutVar => lam.Contributes z).filter fun z => ¬ z.IsInner).card
      = if lam = Term.P0 then 0 else 1 := by
  decide +revert

/-! ### The order of a leaf -/

/-- Membership in the set of levels at which a leaf chooses `P₀`. -/
@[simp]
theorem mem_P0Levels {L : ℕ} {τ : Leaf L} {ℓ : Fin L} : ℓ ∈ P0Levels τ ↔ τ ℓ = Term.P0 := by
  simp [P0Levels]

/-- Membership in the inner set of an output string. -/
@[simp]
theorem mem_innerSetO {L : ℕ} {η : OutStr L} {ℓ : Fin L} : ℓ ∈ innerSetO η ↔ (η ℓ).IsInner := by
  simp [innerSetO]

/-- Section 2.4.3: "A leaf contributing to an output string chooses P₀ only at levels of the output
string's inner set". -/
theorem P0Levels_subset {L : ℕ} {τ : Leaf L} {w : OutStr L} (h : Leaf.Contributes τ w) :
    P0Levels τ ⊆ innerSetO w := by
  intro ℓ hℓ
  rw [mem_P0Levels] at hℓ
  rw [mem_innerSetO]
  rcases (Term.contributes_iff _ _).mp (h ℓ) with hinner | hprivate
  · exact hinner
  · exact (OutVar.privateTerm_eq_P0_iff _).mp (hprivate.symm.trans hℓ)

/-- Section 2.4.3: "so its order is at least 0." -/
theorem order_nonneg {L m : ℕ} {w : OutStr L} (hw : (innerSetO w).card = m) {τ : Leaf L}
    (h : Leaf.Contributes τ w) : 0 ≤ order m τ := by
  have hc := card_le_card (P0Levels_subset h)
  unfold order
  omega

/-- In the proof of Lemma 11: "every leaf of Leaves(U) has an order 0 ≤ d ≤ m".  The upper
bound holds for every leaf. -/
theorem order_le {L : ℕ} (m : ℕ) (τ : Leaf L) : order m τ ≤ m := by
  unfold order
  omega

/-- A leaf has order `d` exactly if it chooses `P₀` at `m - d` levels. -/
theorem order_eq_iff {L : ℕ} (m d : ℕ) (τ : Leaf L) :
    order m τ = d ↔ (P0Levels τ).card + d = m := by
  unfold order
  omega

/-! ### The counts -/

/-- Section 2.4.3: "A single output string has 10^m […] leaves contributing to it." -/
theorem card_filter_contributes {L m : ℕ} (w : OutStr L) (hw : (innerSetO w).card = m) :
    (univ.filter fun τ : Leaf L => Leaf.Contributes τ w).card = 10 ^ m := by
  -- Ten terms contribute to `z₀` and one to `z_ij`.
  simp only [Leaf.filter_contributes_eq_piFinset, Fintype.card_piFinset,
    card_contributing_term]
  rw [prod_ite, prod_const, prod_const_one, mul_one, ← hw]
  rfl

/-- Section 2.4.3: "exactly α_d := binom(m, d) 9^d leaves of order d contribute to an output
string".  As everywhere in Section 2.4.3, the output strings are those whose inner sets have exactly
m elements. -/
theorem sec2_card_contributing_of_order {L m : ℕ} (w : OutStr L) (hw : (innerSetO w).card = m)
    (d : ℕ) :
    (univ.filter fun τ : Leaf L => Leaf.Contributes τ w ∧ order m τ = d).card = alpha m d := by
  by_cases hd : d ≤ m
  · -- Sort the strings of terms that contribute to `w` level by level and have `P₀` at exactly
    -- `m - d` levels by the set `S` of these levels.
    have hcount := Finset.card_pi_places_card
      (fun ℓ => univ.filter fun lam : Term => lam.Contributes (w ℓ)) (fun lam => lam = Term.P0)
      (m - d)
    simp only [card_contributing_P0, card_contributing_ne_P0] at hcount
    -- Given `S`, there is no such string unless `S ⊆ Q`.  Then there are nine choices at each of
    -- the `|Q| - |S| = d` levels of `Q` outside `S`, and one choice at every other level.
    have hgiven : ∀ S ∈ powersetCard (m - d) (univ : Finset (Fin L)),
        (∏ ℓ, if ℓ ∈ S then (if (w ℓ).IsInner then 1 else 0) else (if (w ℓ).IsInner then 9 else 1))
          = if S ⊆ innerSetO w then 9 ^ d else 0 := by
      intro S hS
      have hQS := prod_ite_ite_subset (innerSetO w) S 9
      rw [hw, (mem_powersetCard.mp hS).2, Nat.sub_sub_self hd] at hQS
      rw [← hQS]
      exact prod_congr rfl fun ℓ _ => by simp
    -- There are `binom(m, m - d) = binom(m, d)` sets `S ⊆ Q`.
    rw [sum_congr rfl hgiven, sum_powersetCard_ite_subset, hw, Nat.choose_symm hd] at hcount
    -- These strings are the leaves of order `d` that contribute to `w`.
    rw [alpha, ← hcount]
    refine congrArg card (Finset.ext fun τ => ?_)
    simp only [mem_filter, mem_univ, true_and, order_eq_iff]
    exact and_congr Iff.rfl (by unfold P0Levels; omega)
  · -- No leaf has order more than `m`.
    rw [alpha, Nat.choose_eq_zero_of_lt (by omega), zero_mul, card_eq_zero]
    refine filter_eq_empty_iff.mpr fun τ _ h => ?_
    have hle := order_le m τ
    omega

/-- Section 2.4.3: "The total number of leaves of order d in the entire recursion tree is
β_d := binom(L, m-d) 9^{L-m+d}".

NOTE.  `d ≤ m` and `m ≤ L` are left implicit in the paper. -/
theorem card_filter_order_eq {L m : ℕ} (hmL : m ≤ L) (d : ℕ) (hd : d ≤ m) :
    (univ.filter fun τ : Leaf L => order m τ = d).card = beta L m d := by
  -- The leaves of order `d` are the strings of terms with `P₀` at exactly `m - d` levels.
  have hsort : (univ.filter fun τ : Leaf L => order m τ = d)
      = univ.filter fun τ : Leaf L => (univ.filter fun ℓ => τ ℓ = Term.P0).card = m - d := by
    ext τ
    simp only [mem_filter, mem_univ, true_and, order_eq_iff]
    unfold P0Levels
    omega
  rw [hsort, Finset.card_places_card (fun lam : Term => lam = Term.P0) (m - d), card_term_P0,
    card_term_ne_P0, one_pow, one_mul, Fintype.card_fin, beta,
    show L - (m - d) = L - m + d by omega]

/-- Section 2.4.3: "In particular, β₀ = binom(L, m) 9^{L-m}". -/
theorem beta_zero (L m : ℕ) : beta L m 0 = L.choose m * 9 ^ (L - m) := by
  simp [beta]

/-- Section 2.4.3: "β₀ = binom(L, m) 9^{L-m} = M". -/
theorem beta_zero_eq_M (L m : ℕ) : beta L m 0 = M L m := by
  rw [beta_zero, M, K, N0, ← pow_mul, mul_comm (L - m) 2, pow_mul]
  norm_num

/-- Section 2.4.3: "A leaf of order d contributes to binom(L-m+d, d) output strings, one for each
inner set of size m that contains the m-d levels at which it chooses P₀."  Only the number is
stated.  As everywhere in Section 2.4.3, the output strings are those whose inner sets have exactly
m elements.

NOTE.  `m ≤ L` is left implicit in the paper. -/
theorem sec2_card_outStr_of_leaf {L m : ℕ} (hmL : m ≤ L) (d : ℕ) (τ : Leaf L)
    (hτ : order m τ = d) :
    (univ.filter fun w : OutStr L => (innerSetO w).card = m ∧ Leaf.Contributes τ w).card
      = (L - m + d).choose d := by
  have hP0 : (P0Levels τ).card + d = m := (order_eq_iff m d τ).mp hτ
  -- Sort the output strings to which `τ` contributes level by level, with `z₀` at exactly `m`
  -- levels, by the set `S` of these levels, which is their inner set.
  have hcount := Finset.card_pi_places_card
    (fun ℓ => univ.filter fun z : OutVar => (τ ℓ).Contributes z) (fun z => z.IsInner) m
  simp only [card_contributed_inner, card_contributed_outer] at hcount
  -- Given `S`, there is one such string if `S` contains the levels at which `τ` chooses `P₀`, and
  -- none otherwise.
  have hgiven : ∀ S ∈ powersetCard m (univ : Finset (Fin L)),
      (∏ ℓ, if ℓ ∈ S then 1 else (if τ ℓ = Term.P0 then 0 else 1))
        = if P0Levels τ ⊆ S then 1 else 0 := by
    intro S _
    rw [← prod_ite_ite_superset]
    exact prod_congr rfl fun ℓ _ => by simp
  -- A set of `m` levels that contains these `m - d` levels is given by the `L - m` levels outside
  -- it, among the other `L - m + d` levels.
  rw [sum_congr rfl hgiven, ← card_filter,
    card_powersetCard_superset _ (by simpa using hmL), Fintype.card_fin,
    show L - (P0Levels τ).card = L - m + d by omega, Nat.choose_symm_add] at hcount
  rw [← hcount]
  refine congrArg card (Finset.ext fun w => ?_)
  simp only [mem_filter, mem_univ, true_and]
  exact and_comm

/-- `β_d` is positive when `m ≤ L`. -/
theorem beta_pos {L m : ℕ} (hmL : m ≤ L) (d : ℕ) : 0 < beta L m d :=
  Nat.mul_pos (Nat.choose_pos (by omega)) (by positivity)

/-- The equality in equation (5) without division: `β_d (L-m+d) = 9 (m-d+1) β_{d-1}` for
`1 ≤ d ≤ m ≤ L`. -/
theorem Equation5.ratio_nat {L m : ℕ} (hmL : m ≤ L) (d : ℕ) (hd1 : 1 ≤ d) (hd : d ≤ m) :
    beta L m d * (L - m + d) = 9 * (m - d + 1) * beta L m (d - 1) := by
  -- With `k = m - d` this is `binom(L, k) (L - k) = binom(L, k + 1) (k + 1)`, times a power of 9.
  have hchoose : L.choose (m - d + 1) * (m - d + 1) = L.choose (m - d) * (L - m + d) := by
    rw [Nat.choose_succ_right_eq, show L - (m - d) = L - m + d by omega]
  have hpow : 9 ^ (L - m + d) = 9 * 9 ^ (L - m + (d - 1)) := by
    rw [show L - m + d = L - m + (d - 1) + 1 by omega, pow_succ, mul_comm]
  rw [beta, beta, show m - (d - 1) = m - d + 1 by omega, hpow]
  calc L.choose (m - d) * (9 * 9 ^ (L - m + (d - 1))) * (L - m + d)
      = 9 * 9 ^ (L - m + (d - 1)) * (L.choose (m - d) * (L - m + d)) := by ring
    _ = 9 * 9 ^ (L - m + (d - 1)) * (L.choose (m - d + 1) * (m - d + 1)) := by rw [hchoose]
    _ = 9 * (m - d + 1) * (L.choose (m - d + 1) * 9 ^ (L - m + (d - 1))) := by ring

/-- Section 2.4.3, the equality in equation (5), for every `L ≥ m` (it is used again as equation (7)
in Section 4.3): "β_d / β_{d-1} = 9(m-d+1) / (L-m+d)" for `1 ≤ d ≤ m`.

NOTE.  The paper prints the equality under `L = 19m` in (5) and under `L ≥ 10m` in (7); here it is
stated for every `L ≥ m`. -/
theorem eq_5_ratio {L m : ℕ} (hmL : m ≤ L) (d : ℕ) (hd1 : 1 ≤ d) (hd : d ≤ m) :
    (beta L m d : ℚ) / (beta L m (d - 1) : ℚ)
      = 9 * ((m : ℚ) - (d : ℚ) + 1) / ((L : ℚ) - (m : ℚ) + (d : ℚ)) := by
  have hm : (m : ℚ) ≤ L := by exact_mod_cast hmL
  have hd0 : (1 : ℚ) ≤ d := by exact_mod_cast hd1
  have hbeta : (0 : ℚ) < beta L m (d - 1) := by exact_mod_cast beta_pos hmL (d - 1)
  have hnat := congrArg (Nat.cast : ℕ → ℚ) (Equation5.ratio_nat hmL d hd1 hd)
  push_cast [Nat.cast_sub hmL, Nat.cast_sub hd] at hnat
  rw [div_eq_div_iff hbeta.ne' (by linarith), hnat]

/-- Section 2.4.3, the inequalities in equation (5): "if L = 19m, then for 1 ≤ d ≤ m we have
β_d / β_{d-1} = 9(m-d+1)/(L-m+d) ≤ 9m/(18m+1) < 1/2". -/
theorem eq_5_bound (m d : ℕ) (hd1 : 1 ≤ d) (hd : d ≤ m) :
    (beta (19 * m) m d : ℚ) / (beta (19 * m) m (d - 1) : ℚ) ≤ 9 * (m : ℚ) / (18 * (m : ℚ) + 1)
      ∧ 9 * (m : ℚ) / (18 * (m : ℚ) + 1) < 1 / 2 := by
  have hm : (1 : ℚ) ≤ m := by exact_mod_cast hd1.trans hd
  have hd0 : (1 : ℚ) ≤ d := by exact_mod_cast hd1
  refine ⟨?_, ?_⟩
  · -- The numerator is at most `9m` and the denominator at least `18m + 1`, because `d ≥ 1`.
    rw [eq_5_ratio (by omega) d hd1 hd]
    push_cast
    exact div_le_div₀ (by positivity) (by linarith) (by positivity) (by linarith)
  · rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith

/-- **Equation (5)**, conclusion: if `L = 19m` then "β_d ≤ 2^{-d} M", for `0 ≤ d ≤ m`.
The inequality is multiplied out. -/
theorem eq_5 (m d : ℕ) (hd : d ≤ m) : 2 ^ d * beta (19 * m) m d ≤ M (19 * m) m := by
  induction d with
  | zero => simp [beta_zero_eq_M]
  | succ d ih =>
    -- By the two inequalities of (5), `β_{d+1} < β_d / 2`.
    obtain ⟨hle, hlt⟩ := eq_5_bound m (d + 1) (by omega) hd
    rw [Nat.add_sub_cancel] at hle
    have hbeta : (0 : ℚ) < beta (19 * m) m d := by exact_mod_cast beta_pos (by omega) d
    have hhalf : 2 * beta (19 * m) m (d + 1) ≤ beta (19 * m) m d := by
      have hq := (div_lt_iff₀ hbeta).mp (hle.trans_lt hlt)
      exact_mod_cast (by linarith : (2 * beta (19 * m) m (d + 1) : ℚ) ≤ beta (19 * m) m d)
    calc 2 ^ (d + 1) * beta (19 * m) m (d + 1) = 2 ^ d * (2 * beta (19 * m) m (d + 1)) := by ring
      _ ≤ 2 ^ d * beta (19 * m) m d := Nat.mul_le_mul_left _ hhalf
      _ ≤ M (19 * m) m := ih (by omega)

/-- Figure 6, for `L = 6`, `m = 2` and the output string `w = z₁₃ z₀ z₂₁ z₃₃ z₀ z₁₂` of
Figure 4: its private leaf is `P₁₃ P₀ P₂₁ P₃₃ P₀ P₁₂`, and the numbers of the figure, evaluated:
`α₀ = 1`, `α₁ = 18`, `α₂ = 81`, `binom(5, 1) = 5` and `binom(6, 2) = 15` (the "1 output string" of
the private leaf, `binom(4, 0) = 1`, is left out).  That `α_d` leaves of order `d` contribute to
`w`, and that a leaf of order `d` contributes to `binom(L-m+d, d)` output strings, is stated in
general by `sec2_card_contributing_of_order` and `sec2_card_outStr_of_leaf`. -/
theorem figure_6 :
    privateLeaf (![.z 0 2, .z0, .z 1 0, .z 2 2, .z0, .z 0 1] : OutStr 6)
        = ![.P 0 2, .P0, .P 1 0, .P 2 2, .P0, .P 0 1]
      ∧ alpha 2 0 = 1 ∧ alpha 2 1 = 18 ∧ alpha 2 2 = 81
      ∧ (6 - 2 + 1).choose 1 = 5 ∧ (6 - 2 + 2).choose 2 = 15 := by
  refine ⟨?_, by decide, by decide, by decide, by decide, by decide⟩
  funext ℓ
  fin_cases ℓ <;> rfl

end ThreeSumApsp
