/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Variance.Var
public import Eight.ViaGrouping.Search
import all Eight.SecNetworks_Grouping
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # From the variance of Y to the first good grouping

«… = 4PU ≤ 4gP², and by Chebyshev Pr(Y_{γ,γ'} > U/K² + gP/K³) ≤ 4K⁶/g = 4/(3K²). By a union bound
over the fewer than K²/2 pairs of groups, some pair violates this bound with probability less than
2/3. … so a good grouping exists.» and «Go through all K^g groupings (a constant) and fix the first
good one.» (proof of Lemma 1.)
The proofs are those of proof/networks/Eight/SecNetworks_Grouping.lean (`cheb_Y`, `some_pair`,
`groupingFacts`) and proof/networks/Eight/ViaGrouping/Search.lean (`exists_goodP`, `stSearch`), with
the step before each in its hypotheses; so they rest on the variance of
proof/networks/Variance/Var.lean. The sentences on the sizes of the groups are taken from
SecNetworks_Grouping.lean as they are (`cheb_size`, `some_group`), and so are
`total_le`, `card_pairs_lt`, `Y_symm`, `exists_good_of` and Chebyshev's inequality as a count
(`cheb_count`). `cheb_count` is private in SecNetworks_Grouping.lean; the line
`import all Eight.SecNetworks_Grouping` is there only to reach it. -/

public section

namespace Variance

open Finset Eight.SecNetworks Eight.ViaGrouping

/-- «4PU ≤ 4gP²»: U ≤ gP, by (i) of Definition 2. -/
theorem stTotalLe : StTotalLe := fun _ _ _ hP => total_le hP

/-- Y_{γ,γ'} ≤ U: a sum over some of the ordered pairs. -/
theorem Y_le_total {g K : ℕ} (c : Fin g → Fin g → ℕ) (χ : Fin g → Fin K) {γ γ' : Fin K} (hne : γ ≠ γ') : Y c χ γ γ' ≤ ∑ a, ∑ b ∈ univ.erase a, c a b := by
  rw [stYIsSum g K c χ γ γ' hne, ← sum_ordered_c]
  refine sum_le_sum fun p _ => ?_
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _

/-- «and by Chebyshev Pr(Y_{γ,γ'} > U/K² + gP/K³) ≤ 4K⁶/g», from Var Y ≤ 4PU and U ≤ gP: the
deviation is gP/K³, so the bound is 4gP²·K⁶/(gP)². The proof is that of `Eight.SecNetworks.cheb_Y`,
from the two hypotheses. -/
theorem stChebOfVar : StChebOfVar := by
  intro g K P c γ γ' hne hV hU
  unfold VarBound at hV
  unfold ChebBound
  have hY : ∀ χ : Fin g → Fin K, Y c χ γ γ' ≤ ∑ a, ∑ b ∈ univ.erase a, c a b := fun χ => Y_le_total c χ hne
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

/-- «By a union bound over the fewer than K²/2 pairs of groups, some pair violates this bound with
probability less than» (K²/2)·(4K⁶/g): the union runs over the pairs γ < γ' only, since Y_{γ,γ'} =
Y_{γ',γ}. The proof is that of `Eight.SecNetworks.some_pair`, from the hypothesis. -/
theorem stSomePairOfCheb : StSomePairOfCheb := by
  intro g K P c hK hs hC
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
      _ ≤ ∑ _p : Fin K × Fin K with _p.1 < _p.2, 4 * K ^ 6 * K ^ g := sum_le_sum fun p hp => hC p.1 p.2 (mem_filter.1 hp).2.ne
      _ = _ := by simp
  have h2 : #{p : Fin K × Fin K | p.1 < p.2} * (4 * K ^ 6 * K ^ g) < 2 * K ^ 8 * K ^ g := by
    calc #{p : Fin K × Fin K | p.1 < p.2} * (4 * K ^ 6 * K ^ g) = (2 * #{p : Fin K × Fin K | p.1 < p.2}) * (2 * K ^ 6 * K ^ g) := by ring
      _ < K ^ 2 * (2 * K ^ 6 * K ^ g) := Nat.mul_lt_mul_of_pos_right hlt (by positivity)
      _ = 2 * K ^ 8 * K ^ g := by ring
  exact lt_of_le_of_lt h1 h2

/-- **«A good grouping exists»**: the steps of the paragraph at g = 3K⁸, with the numbers 4/(3K²),
2/3, K/g, 1/3 of the text, from the bound on the variance of Y through Chebyshev and the union bound
over the pairs of groups. -/
theorem stGroupingOf : StGroupingOf := by
  intro hVar hTot hCheb hPair
  have cheb : ∀ (g K P : ℕ) (c : Fin g → Fin g → ℕ), (∀ a b, c a b = c b a) → (∀ a, ∑ b ∈ univ.erase a, c a b ≤ P) → ∀ γ γ' : Fin K, γ ≠ γ' → ChebBound c P γ γ' :=
    fun g K P c hs hP γ γ' hne => hCheb g K P c γ γ' hne (hVar g K P c hs hP γ γ' hne) (hTot g P c hP)
  have pairs : ∀ (K P : ℕ) (c : Fin (3 * K ^ 8) → Fin (3 * K ^ 8) → ℕ), 2 ≤ K → (∀ a b, c a b = c b a) → (∀ a, ∑ b ∈ univ.erase a, c a b ≤ P) →
      3 * #{χ : Fin (3 * K ^ 8) → Fin K | ∃ γ γ', γ ≠ γ' ∧ K * (∑ a, ∑ b ∈ univ.erase a, c a b) + 3 * K ^ 8 * P < K ^ 3 * Y c χ γ γ'} < 2 * K ^ (3 * K ^ 8) := by
    intro K P c hK hs hP
    have h := hPair (3 * K ^ 8) K P c (by omega) hs (cheb _ K P c hs hP)
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
    have h' : K ^ 6 * (3 * #{χ : Fin (3 * K ^ 8) → Fin K | ∃ γ, 2 * (3 * K ^ 8) < K * #{a | χ a = γ}}) ≤ K ^ (3 * K ^ 8) := by
      refine Nat.le_of_mul_le_mul_left ?_ h2
      calc _ = 3 * K ^ 8 * #{χ : Fin (3 * K ^ 8) → Fin K | ∃ γ, 2 * (3 * K ^ 8) < K * #{a | χ a = γ}} := by ring
        _ ≤ _ := h
    rcases Nat.eq_zero_or_pos (3 * #{χ : Fin (3 * K ^ 8) → Fin K | ∃ γ, 2 * (3 * K ^ 8) < K * #{a | χ a = γ}}) with h0 | hp
    · rw [h0]; exact hN
    · exact lt_of_lt_of_le (by nlinarith) h'
  refine ⟨?_, pairs, fun K _ γ => cheb_size γ, groups, fun K P c hK hs hP => exists_good_of (pairs K P c hK hs hP) (groups K hK)⟩
  intro K P c hK hs hP γ γ' hne
  have h : ChebBound c P γ γ' := cheb _ K P c hs hP γ γ' hne
  unfold ChebBound at h
  have h6 : 0 < K ^ 6 := pow_pos (by omega) 6
  refine Nat.le_of_mul_le_mul_left ?_ h6
  calc _ = 3 * K ^ 8 * #{χ : Fin (3 * K ^ 8) → Fin K | K * (∑ a, ∑ b ∈ univ.erase a, c a b) + 3 * K ^ 8 * P < K ^ 3 * Y c χ γ γ'} := by ring
    _ ≤ 4 * K ^ 6 * K ^ (3 * K ^ 8) := h
    _ = _ := by ring

/-- «A good grouping exists», with the numbers of the text, on the variance summed from the
covariances. (Not the theorem of the same name in `Eight.SecNetworks`.) -/
theorem groupingFacts : GroupingFacts := stGroupingOf stVar stTotalLe stChebOfVar stSomePairOfCheb

/-- **«Go through all K^g groupings (a constant) and fix the first good one.»** For g = 3K⁸ there is
a first number x < K^g to which the test says yes, and the grouping number x is good as printed;
from «a good grouping exists». -/
theorem stSearchOfGrouping : StSearchOfGrouping := by
  intro hG K hK C _ Np c N P B τ S h
  have hK0 : 0 < K := by omega
  obtain ⟨x', hx', hgood'⟩ : ∃ x < K ^ (3 * K ^ 8), goodP K (3 * K ^ 8) Np (c, x) = true := by
    obtain ⟨χ, hχ⟩ := hG.exists_good K P N.c hK h.is.c_symm h.is.i
    obtain ⟨x, hx, rfl⟩ := grouping_number hK0 χ
    exact ⟨x, hx, (goodP_iff hK0 h x).2 hχ⟩
  obtain ⟨x, hfind⟩ : ∃ x, (List.range (K ^ (3 * K ^ 8))).find? (fun x => goodP K (3 * K ^ 8) Np (c, x)) = some x := by
    rw [← Option.isSome_iff_exists, List.find?_isSome]
    exact ⟨x', List.mem_range.2 hx', hgood'⟩
  have hgood : goodP K (3 * K ^ 8) Np (c, x) = true := List.find?_some (p := fun x => goodP K (3 * K ^ 8) Np (c, x)) hfind
  exact ⟨x, List.mem_range.1 (List.mem_of_find?_eq_some hfind), hfind, (goodP_iff _ h x).1 hgood⟩

/-- «Go through all K^g groupings (a constant) and fix the first good one», on the variance summed
from the covariances. (Not the theorem of the same name in `Eight.ViaGrouping`.) -/
theorem stSearch : Eight.ViaGrouping.StSearch := stSearchOfGrouping Variance.groupingFacts

end Variance
