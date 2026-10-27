/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Coding.Defs
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Ring

/-! # Sets for lists

Section 6: «a clause is a nonempty set of literals, and a 3-CNF is a finite set of clauses with at
most 3 literals each». The end statement of this development, `Sat3.ThmEveryDelta`, has lists. Here:
every 3-CNF in the printed sense can be written as a list of lists; whatever writes it is an
instance in the sense of the end statement and is satisfiable exactly if the 3-CNF is (`stWrites`);
so 3-SAT is decided within c·2^{δn} steps for every δ > 0 also for 3-CNFs as sets, in whichever way
the set is written on the tape (`stSetFormOf`). And Section 3, Conventions: «a 3-CNF is a set of
clauses (Section 6), so m = O(n³)» (`stCubic`). -/

public section

namespace Coding

open Finset

/-- «a clause is a nonempty set of literals, and a 3-CNF is a finite set of clauses with at most 3
literals each» (Section 6): every such set can be written as a list of lists, and whatever writes it
is an instance of the end statement with as many clauses, without an empty clause, and satisfiable
exactly if the set is. -/
theorem stWrites : StWrites := by
  intro n Φ
  constructor
  · have e : (Φ.clauses.toList.map Finset.toList).map List.toFinset = Φ.clauses.toList := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id Φ.clauses.toList]
      exact List.map_congr_left fun E _ => Finset.toList_toFinset E
    refine ⟨Φ.clauses.toList.map Finset.toList, ?_, ?_, ?_⟩
    · intro C hC
      obtain ⟨E, -, rfl⟩ := List.mem_map.1 hC
      exact Finset.nodup_toList E
    · rw [e]; exact Finset.nodup_toList _
    · rw [e]; exact Finset.toList_toFinset _
  · rintro φ ⟨h1, h2, h3⟩
    have hmem : ∀ C ∈ φ, C.toFinset ∈ Φ.clauses := fun C hC => h3 ▸ List.mem_toFinset.2 (List.mem_map_of_mem hC)
    refine ⟨⟨fun C hC => ?_, List.Nodup.of_map _ h2⟩, ?_, fun hnil => ?_, ?_, ?_⟩
    · rw [← List.toFinset_card_of_nodup (h1 C hC)]
      exact Φ.width _ (hmem C hC)
    · rw [← h3, List.toFinset_card_of_nodup h2, List.length_map]
    · simpa using Φ.nonempty _ (hmem [] hnil)
    · rintro ⟨a, ha⟩
      refine ⟨a, fun E hE => ?_⟩
      rw [← h3, List.mem_toFinset] at hE
      obtain ⟨C, hC, rfl⟩ := List.mem_map.1 hE
      obtain ⟨l, hl, h⟩ := ha C hC
      exact ⟨l, List.mem_toFinset.2 hl, h⟩
    · rintro ⟨a, ha⟩
      refine ⟨a, fun C hC => ?_⟩
      obtain ⟨l, hl, h⟩ := ha _ (hmem C hC)
      exact ⟨l, List.mem_toFinset.1 hl, h⟩

/-- **3-SAT in time c·2^{δn} for every δ > 0, for 3-CNFs as sets** (Section 6: «a 3-CNF is a finite
set of clauses with at most 3 literals each»), from the same for lists and from `StWrites` (lists
write sets). -/
theorem stSetFormOf : StSetFormOf := by
  intro HW H2 δ hδ
  obtain ⟨M, c, hfin, h⟩ := H2 δ hδ
  refine ⟨M, c, hfin, fun n Φ φ hφ => ?_⟩
  obtain ⟨h3, -, -, hsat⟩ := (HW n Φ).2 φ hφ
  obtain ⟨b, t, hb, ht, hh⟩ := h n φ h3
  exact ⟨b, t, hb.trans hsat, ht, hh⟩

/-- «a 3-CNF is a set of clauses (Section 6), so m = O(n³)» (Section 3, Conventions): the clauses
are among the sets of 1, 2 or 3 of the 2n literals. -/
theorem stCubic : StCubic := by
  intro n Φ
  have hU : (univ : Finset (Sat3.Lit n)).card = 2 * n := by
    rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.mul_comm]
  have hsub : Φ.clauses ⊆ powersetCard 1 univ ∪ powersetCard 2 univ ∪ powersetCard 3 univ := by
    intro E hE
    have h1 := Finset.card_pos.2 (Φ.nonempty E hE)
    have h2 := Φ.width E hE
    simp only [mem_union, mem_powersetCard, subset_univ, true_and]
    omega
  have h := (card_le_card hsub).trans ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _))
  rw [card_powersetCard, card_powersetCard, card_powersetCard, hU] at h
  have c1 := Nat.choose_le_pow (2 * n) 1
  have c2 := Nat.choose_le_pow (2 * n) 2
  have c3 := Nat.choose_le_pow (2 * n) 3
  have e1 : (2 * n) ^ 1 = 2 * n := by ring
  have e2 : (2 * n) ^ 2 = 4 * n ^ 2 := by ring
  have e3 : (2 * n) ^ 3 = 8 * n ^ 3 := by ring
  have p2 : n ^ 2 ≤ n ^ 3 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact Nat.pow_le_pow_right hn (by omega)
  have p1 : n ≤ n ^ 3 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · calc n = n ^ 1 := (pow_one n).symm
        _ ≤ n ^ 3 := Nat.pow_le_pow_right hn (by omega)
  omega

end Coding
