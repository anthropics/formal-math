/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ExplicitCost.EntryDefs
import ExplicitCost.SameRuns
import Printed.GroupingEntry
import Printed.Close
import Printed.Coding
import QueryMachines.Runs
import Mathlib.Tactic

/-! # The cost of an entry, with one constant for all K and g

`entryCostExplicit : EntryCostExplicit`, with c₁ = 10. The count of the steps is taken from results
proved elsewhere in this development:
* `Eight.ViaGrouping.Table.tableM_runs` (proof/networks/Eight/ViaGrouping/Table.lean): if every
  group has at most m nodes (here m = ⌊2g/K⌋), the step machine for an entry takes at most
  2^{Pm}·(g²(4τ + 4) + 1) steps, EXPLICIT numbers, and its states are bounded by a sum of products
  of K, g, P, B, L and of sizes. (The constant that depends on K and g enters only in
  `tableM_runs_coarse`.)
* With one-step procedures («ask», with the oracle built in: `Printed.asked_isNetworkP`) this is a
  count of own steps and queries of `Printed.tableQ K g asked` (`Printed.tableQ_close`,
  `QueryMachines.stClose`); at τ operations for a query it is multiplied by τ
  (`QueryMachines.stSlowDown`): `tableQ_within_explicit`.
* The machine that reads K and g runs step for step as `tableQ K g asked`, on states larger by four
  copies of K and g in unary (`mirrors_entryData`).
* For 1 ≤ K ≤ g, x < K^g and L ≤ 2gP all of this is at most (g(P+B))^{10} (`factor_le`,
  `states_le`): each of the two is at most 256·(g(P+B))², and g(P+B) ≥ 2 (`Sizes.sq_le_pow`).
The value of the entry and the strict bound |W̃_γ| < 2^{B'} do not depend on how K and g are given;
they are taken from proof/threesat/Printed (`Printed.stToLists`, `Printed.abs_display_lt`). -/

public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed

/-! ## The entry, and its count with explicit numbers -/

/-- The integer that the step machine for an entry returns is the display of W̃_γ(Θ). -/
theorem mergedVal_eq_display {C : Type} [HasSize C] {K g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ} (h : IsNetworkP Np c N P B τ S) (hK0 : 0 < K) (x L : ℕ)
    (hY : ∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L) (γ : Fin K) (θ : Fin K → List Bool) (hθ : ∀ γ', γ' ≠ γ → (θ γ').length = L) :
    mergedVal K g Np.toPaperNetwork N.toPaperNetwork ((c, x), (γ.val, List.ofFn θ)) = display Np c N hK0 x γ θ := by
  rw [← groupedTables_eq_display h hK0 x L hY γ θ hθ, Paper.groupedTables, toInst_eq_mergedVal Np.toPaperNetwork hK0 (Table.isPaperNetwork h).presented x L γ θ hθ]

/-- The display reads only the numbers P_a, c_{a,b} of the procedures. -/
theorem display_close {K g : ℕ} (O : NetQuery → Option ℤ) (c : NetInput) (N : Net g) (hK0 : 0 < K) (x : ℕ) : display (asked.close O) c N hK0 x = display asked.under c N hK0 x := rfl

/-- **The machine of Lemma 1 for K and g, with explicit numbers**: an entry costs at most
2^{P⌊2g/K⌋}·(8g² + 1)·τ operations. -/
theorem tableQ_within_explicit {K g : ℕ} (hK0 : 0 < K) (N : Net g) {P B τ : ℕ} (hN : N.Is P B) (hτ : 1 ≤ τ) (x L : ℕ)
    (hG1 : ∀ γ : Fin K, K * #{a : Fin g | Paper.grouping hK0 x a = γ} ≤ 2 * g) (hY : ∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L) (γ : Fin K) {Θ : List Bool} (hΘ : Θ ∈ words ((K - 1) * L)) :
    (tableQ K g asked).Within (netOracle N) (fun _ => τ) ((netInput N P B, x), toLists K L (γ.val, Θ)) (2 ^ (P * (2 * g / K)) * (g * g * 8 + 1) * τ)
      (size (netInput N P B) + 2 * size g + 4 * P + B + 4 + 4 * (size (netInput N P B) + size x + size K + K * (2 * L + 2)) + 5 * (P * (2 * g / K)) + 2 * (B * (g * g)) + 3 * size (g * g) + 30)
      ((Value.groupClique asked.under (netInput N P B) N hK0 x L).W γ Θ) := by
  have hnet := asked_isNetworkP N hN
  obtain ⟨e1, e2, -⟩ := stToLists K L γ Θ hΘ
  have hθ : ∀ γ', γ' ≠ γ → ((fun u : Fin K => if u = γ then [] else copyAt L γ u Θ) γ').length = L := fun γ' hne => by
    simp only [if_neg hne]
    exact e2 γ' hne
  have hγ : (fun u : Fin K => if u = γ then [] else copyAt L γ u Θ) γ = [] := if_pos rfl
  have hmem : ∀ G < K, (members K g x G).length ≤ 2 * g / K := fun G hG => by
    rw [length_members hK0 x ⟨G, hG⟩, Nat.le_div_iff_mul_le hK0, Nat.mul_comm]
    exact hG1 ⟨G, hG⟩
  have hlb : ∀ G < K, ∀ G' < K, G ≠ G' → lbLen K g (asked.close (netOracle N)).toPaperNetwork (netInput N P B) x G G' ≤ L := fun G hG G' hG' hne => by
    have hne' : (⟨G, hG⟩ : Fin K) ≠ ⟨G', hG'⟩ := fun e => hne (congrArg Fin.val e)
    rw [Table.lbLen_eq_Y hnet hK0 x hne']
    exact hY _ _ hne'
  have hrun := Table.tableM_runs hnet (2 * g / K) hmem hlb hθ hγ
  rw [mergedVal_eq_display hnet hK0 x L hY γ _ hθ, display_close, ← tableQ_close] at hrun
  rw [e1]
  exact stSlowDown _ _ _ _ _ _ _ _ _ τ _ hτ ((stClose _ _ _ _ _ _ _ _ _ _).1 hrun)

/-! ## The arithmetic -/

namespace Sizes

/-- 256·X² ≤ X^{10} for X ≥ 2. -/
theorem sq_le_pow {X : ℕ} (hX : 2 ≤ X) : 256 * (X * X) ≤ X ^ 10 :=
  calc 256 * (X * X) = 2 ^ 8 * (X * X) := by norm_num
    _ ≤ X ^ 8 * (X * X) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hX 8)
    _ = X ^ 10 := by ring

/-- What is used of g, P, B: with q = P + B, X = g·q and A = g²·q. -/
theorem basic_facts {g P B : ℕ} (hg : 1 ≤ g) (hP : 1 ≤ P) (hB : 1 ≤ B) :
    2 * g ≤ g * (P + B) ∧ P + B ≤ g * (P + B) ∧ g * g ≤ g * g * (P + B) ∧ g * g * P ≤ g * g * (P + B) ∧ B * (g * g) ≤ g * g * (P + B) ∧
      g * g * (P + B) ≤ g * (P + B) * (g * (P + B)) ∧ 2 * (g * (P + B)) ≤ g * (P + B) * (g * (P + B)) := by
  have h1 : 2 * g ≤ g * (P + B) := by
    rw [Nat.mul_comm 2 g]
    exact Nat.mul_le_mul_left _ (by omega)
  refine ⟨h1, Nat.le_mul_of_pos_left _ hg, Nat.le_mul_of_pos_right _ (by omega), Nat.mul_le_mul_left _ (by omega), ?_, ?_, Nat.mul_le_mul_right _ (by omega)⟩
  · rw [Nat.mul_comm B]
    exact Nat.mul_le_mul_left _ (by omega)
  · calc g * g * (P + B) = g * g * (P + B) * 1 := (Nat.mul_one _).symm
      _ ≤ g * g * (P + B) * (P + B) := Nat.mul_le_mul_left _ (by omega)
      _ = g * (P + B) * (g * (P + B)) := by ring

end Sizes

open Sizes

/-- «each a product of at most g² values»: the factor 8g² + 1 is at most (g(P+B))^{10}. -/
private theorem factor_le {g P B : ℕ} (hg : 1 ≤ g) (hP : 1 ≤ P) (hB : 1 ≤ B) : g * g * 8 + 1 ≤ (g * (P + B)) ^ 10 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := basic_facts hg hP hB
  refine le_trans ?_ (sq_le_pow (X := g * (P + B)) (by omega))
  omega

/-- All states have size at most (g(P+B))^{10}. -/
private theorem states_le {K g P B x L sc : ℕ} (hK0 : 0 < K) (hKg : K ≤ g) (hP : 1 ≤ P) (hB : 1 ≤ B) (hx : x < K ^ g) (hL : L ≤ 2 * (g * P)) (hsc : sc ≤ (4 * g ^ 2 + 6 * g + 6) * (P + B)) :
    sc + 2 * size g + 4 * P + B + 4 + 4 * (sc + size x + size K + K * (2 * L + 2)) + 5 * (P * (2 * g / K)) + 2 * (B * (g * g)) + 3 * size (g * g) + 30 + 4 * (2 * K + 2 * g + 2) ≤ (g * (P + B)) ^ 10 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := basic_facts (hK0.trans_le hKg) hP hB
  refine le_trans ?_ (sq_le_pow (X := g * (P + B)) (by omega))
  have s1 : sc ≤ 4 * (g * g * (P + B)) + 6 * (g * (P + B)) + 6 * (P + B) := by
    have : (4 * g ^ 2 + 6 * g + 6) * (P + B) = 4 * (g * g * (P + B)) + 6 * (g * (P + B)) + 6 * (P + B) := by ring
    omega
  have s2 := size_nat_le g
  have s3 := size_nat_le K
  have s4 := size_nat_le (g * g)
  have s5 : size x ≤ g * g + 1 := by
    rw [size_nat]
    refine Nat.succ_le_succ (Nat.size_le.2 (hx.trans_le ?_))
    calc K ^ g ≤ (2 ^ g) ^ g := Nat.pow_le_pow_left (hKg.trans Nat.lt_two_pow_self.le) g
      _ = 2 ^ (g * g) := (pow_mul 2 g g).symm
  have s6 : K * (2 * L + 2) ≤ 4 * (g * g * P) + 2 * g := by
    calc K * (2 * L + 2) ≤ g * (2 * (2 * (g * P)) + 2) := Nat.mul_le_mul hKg (by omega)
      _ = 4 * (g * g * P) + 2 * g := by ring
  have s7 : P * (2 * g / K) ≤ 2 * (g * (P + B)) := by
    calc P * (2 * g / K) ≤ (P + B) * (2 * g) := Nat.mul_le_mul (by omega) (Nat.div_le_self _ _)
      _ = 2 * (g * (P + B)) := by ring
  omega

/-! ## The statement -/

/-- **The cost of an entry, with one constant**: c₁ = 10, for all K, g and all networks. -/
theorem entryCostExplicit : EntryCostExplicit := by
  refine ⟨10, fun K g hK0 N P B τ hKg hN hτ x hx L hL hG1 hY γ Θ hΘ => ⟨?_, ?_⟩⟩
  · refine ((mirrors_entryData K g).within (tableQ_within_explicit hK0 N hN hτ x L hG1 hY γ hΘ)).mono ?_ (states_le hK0 hKg hN.P_pos hN.B_pos hx hL (size_netInput_le N hN))
    calc 2 ^ (P * (2 * g / K)) * (g * g * 8 + 1) * τ = 2 ^ (P * (2 * g / K)) * τ * (g * g * 8 + 1) := by ring
      _ ≤ 2 ^ (P * (2 * g / K)) * τ * (g * (P + B)) ^ 10 := Nat.mul_le_mul_left _ (factor_le (hK0.trans_le hKg) hN.P_pos hN.B_pos)
  · obtain ⟨-, e2, -⟩ := stToLists K L γ Θ hΘ
    exact abs_display_lt (asked_isNetworkP N hN) hK0 (hK0.trans_le hKg) x L hG1 hY γ (fun u : Fin K => if u = γ then [] else copyAt L γ u Θ) fun γ' hne => by
      simp only [if_neg hne]
      exact e2 γ' hne

end ExplicitCost
