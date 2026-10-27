/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ExplicitCost.GroupingDefs
import ExplicitCost.GroupingNumbers
import ExplicitCost.Cost
import Printed.GroupingEntry
import GeneralPieces.Main
import Exits.Runs
import Exits.Tested
import Eight.ViaGrouping.Search
import Mathlib.Tactic

/-! # «find the first such grouping among all K^g»

* `goodData_iff`: on the input that belongs to ζ = a/b, K and a network N, the test of the procedure
  says yes to the number y exactly if the grouping number y has at most 2g/K nodes in every group
  and Y_{γ,γ'} ≤ L for all γ ≠ γ'.
* `searchFinds`: in case (i) or (ii) some grouping is such (`AppRunningTime.someGrouping`), every
  grouping has a number below K^g, so there is a first number that the test accepts.
* `Sizes.search_sizes`: the arithmetic of the sizes of the states.
* `searchCost`: the loop halts at the first number x that the test accepts, after 2·(x + 1) ≤ 2·K^g
  steps (`Exits.stFirstUntil`; a test is one step). The constant is 10. -/

public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed

/-- The test of the procedure says yes to y exactly if the grouping number y has the two properties. -/
theorem goodData_iff {a b K g : ℕ} (hK0 : 0 < K) {N : Net g} {P B : ℕ} (hb : 0 < b) (hab : a ≤ b) (hN : N.Is P B) (y : ℕ) :
    goodData (groupingInput a b K N P B, y) = true ↔
      (∀ γ : Fin K, K * #{v : Fin g | Paper.grouping hK0 y v = γ} ≤ 2 * g) ∧ ∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 y) γ γ' ≤ AppRunningTime.Lof K g ((a : ℝ) / b) P N.U := by
  simp only [goodData, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq]
  rw [inK_groupingInput, inG_groupingInput, (labelLengthIsL a b K g N P B hb hab hK0 hN).1]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun γ => ?_, fun γ γ' hne => ?_⟩
    · have := h1 γ.val γ.2
      rwa [length_members hK0 y γ] at this
    · rw [← lbLen_groupingInput a b K N hK0 hN y hne]
      exact (h2 γ.val γ.2 γ'.val γ'.2).resolve_left fun e => hne (Fin.ext e)
  · rintro ⟨h1, h2⟩
    refine ⟨fun G hG => ?_, fun G hG G' hG' => ?_⟩
    · rw [length_members hK0 y ⟨G, hG⟩]
      exact h1 _
    · by_cases e : G = G'
      · exact .inl e
      · right
        have hne : (⟨G, hG⟩ : Fin K) ≠ ⟨G', hG'⟩ := fun e' => e (congrArg Fin.val e')
        have := h2 _ _ hne
        rwa [← lbLen_groupingInput a b K N hK0 hN y hne] at this

/-- In case (i) or (ii) the search finds a grouping: there is a first x < K^g that the test accepts,
and its grouping has the two properties. -/
theorem searchFinds : SearchFinds := by
  intro a b K g hK0 N P B hK hg ha hab hN hC
  have hb : 0 < b := by omega
  have hζ0 : (0 : ℝ) < (a : ℝ) / b := div_pos (by exact_mod_cast ha) (by exact_mod_cast hb)
  have hζ1 : (a : ℝ) / b ≤ 1 := (div_le_one (by exact_mod_cast hb)).2 (by exact_mod_cast hab)
  obtain ⟨χ, h1, h2⟩ := AppRunningTime.someGrouping K g _ P N.c hK hg hζ0 hζ1 hN.P_pos hN.c_symm hN.i hC
  obtain ⟨x', hx', rfl⟩ := grouping_number hK0 χ
  have hgood' : goodData (groupingInput a b K N P B, x') = true := (goodData_iff hK0 hb hab hN x').2 ⟨h1, h2⟩
  obtain ⟨x, hfind⟩ : ∃ x, (List.range (K ^ g)).find? (fun y => goodData (groupingInput a b K N P B, y)) = some x := by
    rw [← Option.isSome_iff_exists, List.find?_isSome]
    exact ⟨x', List.mem_range.2 hx', hgood'⟩
  have hgood : goodData (groupingInput a b K N P B, x) = true := List.find?_some (p := fun y => goodData (groupingInput a b K N P B, y)) hfind
  obtain ⟨g1, g2⟩ := (goodData_iff hK0 hb hab hN x).1 hgood
  exact ⟨x, List.mem_range.1 (List.mem_of_find?_eq_some hfind), hfind, g1, g2⟩

namespace Sizes

/-- K^g has at most g² + 1 binary digits, for K ≤ g. -/
theorem size_pow_le {K g : ℕ} (hKg : K ≤ g) : size (K ^ g) ≤ g * g + 2 := by
  rw [size_nat]
  refine Nat.succ_le_succ (Nat.size_le.2 ?_)
  calc K ^ g ≤ (2 ^ g) ^ g := Nat.pow_le_pow_left (hKg.trans Nat.lt_two_pow_self.le) g
    _ = 2 ^ (g * g) := (pow_mul 2 g g).symm
    _ < 2 ^ (g * g + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)

end Sizes

/-- The size of the input of the procedure. -/
theorem size_groupingInput (a b K : ℕ) {g : ℕ} (N : Net g) (P B : ℕ) :
    size (groupingInput a b K N P B) = size (a, b) + (2 * K + 2 * g + 2 + size (netInput N P B)) := by
  have e : size (groupingInput a b K N P B) = size (a, b) + (size (unary K) + size (unary g) + size (netInput N P B)) := rfl
  rw [e, size_unary, size_unary]
  omega

namespace Sizes

/-- With X = g(P+B), s the length of ζ and 1 ≤ K ≤ g: four copies of the input, four of K^g and 40
more units are at most (X + s)², hence at most (X + s)^10. -/
theorem search_sizes {K g P B s sc sk : ℕ} (hK0 : 0 < K) (hKg : K ≤ g) (hP : 1 ≤ P) (hB : 1 ≤ B) (hsc : sc ≤ (4 * g ^ 2 + 6 * g + 6) * (P + B)) (hsk : sk ≤ g * g + 2) :
    4 * (s + (2 * K + 2 * g + 2 + sc)) + 4 * sk + 40 ≤ (g * (P + B) + s) ^ 10 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := basic_facts (hK0.trans_le hKg) hP hB
  refine le_trans ?_ (sq_le_pow (X := g * (P + B) + s) (by omega))
  have s1 : sc ≤ 4 * (g * g * (P + B)) + 6 * (g * (P + B)) + 6 * (P + B) := by
    have : (4 * g ^ 2 + 6 * g + 6) * (P + B) = 4 * (g * g * (P + B)) + 6 * (g * (P + B)) + 6 * (P + B) := by ring
    omega
  have e : (g * (P + B) + s) * (g * (P + B) + s) = g * (P + B) * (g * (P + B)) + 2 * (g * (P + B) * s) + s * s := by ring
  have s2 : 2 * s ≤ g * (P + B) * s := Nat.mul_le_mul_right _ (by omega)
  have s3 : 4 ≤ g * (P + B) * (g * (P + B)) := by
    have : 2 * 2 ≤ g * (P + B) * (g * (P + B)) := Nat.mul_le_mul (by omega) (by omega)
    omega
  rw [e]
  omega

end Sizes

open Sizes

/-- The search takes at most 10·K^g steps, on states of size at most (g(P+B) + the length of
ζ)^{10}. -/
theorem searchCost : SearchCost := by
  refine ⟨10, fun a b K g N P B x hK hKg hN hfind => ?_⟩
  have hx : x < K ^ g := List.mem_range.1 (List.mem_of_find?_eq_some hfind)
  obtain ⟨c, hc⟩ : ∃ c, c = groupingInput a b K N P B := ⟨_, rfl⟩
  rw [← hc] at hfind ⊢
  have hNa : inK c ^ inG c = K ^ g := by rw [hc, inK_groupingInput, inG_groupingInput]
  have hrun := Exits.stFirstUntil GroupingInput Bool (fun c => inK c ^ inG c) (Stepped.ofFun goodData) id c (fun _ => 1) (fun y => goodData (c, y)) (size c + size (K ^ g) + 1)
    (fun y hy => (Stepped.ofFun_runs goodData (c, y)).mono le_rfl (by
      have h1 : y ≤ K ^ g := (hy.le.trans (Exits.reach_le _ _)).trans_eq hNa
      have h2 := Nat.size_le_size h1
      simp only [size_prod, size_nat, size_bool]
      omega))
  simp only [id_eq, hNa] at hrun
  have hreach : Exits.reach (fun y => goodData (c, y)) (K ^ g) = x + 1 := by
    unfold Exits.reach
    rw [hfind]
  rw [hreach, hfind] at hrun
  refine hrun.mono ?_ ?_
  · simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    omega
  · have h := search_sizes (s := size (a, b)) hK hKg hN.P_pos hN.B_pos (size_netInput_le N hN) (size_pow_le hKg)
    have e := size_groupingInput a b K N P B
    rw [← hc] at e
    omega

end ExplicitCost
