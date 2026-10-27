/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Coding.OccMore
import all StepMachines.Prog.CountNet
import Eight.SecProof_Network

/-! # «An occurrence lies in at most two tests …»

Section 6: «An occurrence lies in at most two tests. The total number of tests is the number of
occurrences minus the number of variables that occur, hence at most 3m − 1.» This development proves
these sentences for tests as pairs of places (`Eight.card_tests_at_le_two`,
`Eight.card_testsOf_add`, proof/networks/Eight/SecProof_Network.lean).
Here they are carried over to `Coding.tests`, the list of pairs of occurrences, along the map that
sends a place with a literal to its occurrence; all of Φ is taken as one cluster. The map is one to
one, goes onto the occurrences, and carries Lean's links to the tests (`mem_tests_iff`,
`linkB_iff`). `import all StepMachines.Prog.CountNet` gives access to `linkB_iff` and `litAt_idx`,
which are not public. -/

public section

namespace Coding

open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Groundwork.SatNet Eight

variable {Φ : Fml}

/-- The pair (clause, position) of a place, all of Φ being one cluster. -/
@[expose] def occOfSlot {m : ℕ} (p : Slot 1 m 3) : ℕ × ℕ := (p.2.1.val, p.2.2.val)

/-- The place of the pair of a slot is the index that Lean's network gives the slot. -/
theorem place_occOfSlot {m : ℕ} (p : Slot 1 m 3) : place (occOfSlot p) = idx p := by
  have h : p.1.val = 0 := by have := p.1.2; omega
  simp only [place, occOfSlot, idx, h, Nat.zero_mul, Nat.zero_add]

/-- Different slots have different pairs. -/
theorem occOfSlot_injective {m : ℕ} : Function.Injective (occOfSlot (m := m)) := fun p q h =>
  idx_injective (by rw [← place_occOfSlot, ← place_occOfSlot, h])

/-- Every occurrence is the pair of some slot. -/
theorem exists_occOfSlot (h3 : ∀ C ∈ Φ, C.length ≤ 3) {o : ℕ × ℕ} (ho : o ∈ occAll Φ) : ∃ p : Slot 1 Φ.length 3, occOfSlot p = o :=
  ⟨(0, ⟨o.1, fst_lt_of_mem_occAll ho⟩, ⟨o.2, lt_of_lt_of_le (mem_occAll.1 ho) (length_getD_le h3 o.1)⟩), rfl⟩

/-- A place holds a literal exactly if its pair is an occurrence. -/
theorem mem_occurrencesOf_iff (p : Slot 1 Φ.length 3) : p ∈ occurrencesOf Φ 1 Φ.length 3 ↔ occOfSlot p ∈ occAll Φ := by
  have hj := p.2.2.2
  have e1 : place (occOfSlot p) / 3 = (occOfSlot p).1 := by simp only [place, occOfSlot]; omega
  have e2 : place (occOfSlot p) % 3 = (occOfSlot p).2 := by simp only [place, occOfSlot]; omega
  rw [mem_occurrencesOf, ← litAt_idx, ← place_occOfSlot, litAt_eq, e1, e2, mem_occAll]
  by_cases h : (occOfSlot p).2 < (Φ.getD (occOfSlot p).1 []).length
  · rw [if_pos h]
    exact ⟨fun _ => h, fun _ => Option.some_ne_none _⟩
  · rw [if_neg h]
    exact ⟨fun e => absurd rfl e, fun e => absurd e h⟩

/-- A pair of places is a link exactly if the pair of their occurrences is a test. -/
theorem mem_tests_iff_link (h3 : ∀ C ∈ Φ, C.length ≤ 3) (p q : Slot 1 Φ.length 3) : (occOfSlot p, occOfSlot q) ∈ tests Φ ↔ Link Φ p q := by
  rw [mem_tests_iff h3, place_occOfSlot, place_occOfSlot, linkB_iff (by omega)]
  refine ⟨fun h => h.2.2, fun l => ⟨?_, ?_, l⟩⟩
  · refine (mem_occurrencesOf_iff p).1 (mem_occurrencesOf.2 fun h => l.2.1 ?_)
    rw [lab, h]; rfl
  · refine (mem_occurrencesOf_iff q).1 (mem_occurrencesOf.2 fun h => l.2.1 ?_)
    rw [l.2.2.1, lab, h]; rfl

/-- No test is listed twice. -/
theorem nodup_tests (h3 : ∀ C ∈ Φ, C.length ≤ 3) : (tests Φ).Nodup := ((nodup_occIn h3 0 Φ.length).product (nodup_occIn h3 0 Φ.length)).filter _

/-- The tests are the pairs of the links of Lean's network, taken slot by slot. -/
theorem toFinset_tests (h3 : ∀ C ∈ Φ, C.length ≤ 3) : (tests Φ).toFinset = (testsOf Φ 1 Φ.length 3).image fun t => (occOfSlot t.1, occOfSlot t.2) := by
  ext ⟨o, o'⟩
  simp only [List.mem_toFinset, mem_image, mem_testsOf]
  constructor
  · intro h
    obtain ⟨ho, ho', -⟩ := (mem_tests_iff h3).1 h
    obtain ⟨p, rfl⟩ := exists_occOfSlot h3 ho
    obtain ⟨q, rfl⟩ := exists_occOfSlot h3 ho'
    exact ⟨(p, q), (mem_tests_iff_link h3 p q).1 h, rfl⟩
  · rintro ⟨⟨p, q⟩, l, e⟩
    rw [← e]
    exact (mem_tests_iff_link h3 p q).2 l

/-- The occurrences are the pairs of the slots that hold a literal. -/
theorem toFinset_occAll (h3 : ∀ C ∈ Φ, C.length ≤ 3) : (occAll Φ).toFinset = (occurrencesOf Φ 1 Φ.length 3).image occOfSlot := by
  ext o
  simp only [List.mem_toFinset, mem_image]
  constructor
  · intro ho
    obtain ⟨p, rfl⟩ := exists_occOfSlot h3 ho
    exact ⟨p, (mem_occurrencesOf_iff p).2 ho, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact (mem_occurrencesOf_iff p).1 hp

/-- Inside the list, getD reads the entry. -/
theorem getD_eq_getElem' {α : Type} {l : List α} {i : ℕ} (d : α) (h : i < l.length) : l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; rfl

/-- The variables at the occurrences are the variables that occur. -/
theorem toFinset_vars : ((occAll Φ).map fun o => (litOf Φ o).1).toFinset = occurring Φ := by
  ext v
  simp only [List.mem_toFinset, List.mem_map, mem_occurring]
  constructor
  · rintro ⟨o, ho, rfl⟩
    have h1 := fst_lt_of_mem_occAll ho
    have h2 := mem_occAll.1 ho
    rw [getD_eq_getElem' [] h1] at h2
    refine ⟨Φ[o.1], List.getElem_mem h1, Φ[o.1][o.2], List.getElem_mem h2, ?_⟩
    rw [litOf, getD_eq_getElem' [] h1, getD_eq_getElem' _ h2]
  · rintro ⟨C, hC, l, hl, rfl⟩
    obtain ⟨e, he, rfl⟩ := List.getElem_of_mem hC
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hl
    refine ⟨(e, j), mem_occAll.2 ?_, ?_⟩
    · change j < (Φ.getD e []).length
      rw [getD_eq_getElem' [] he]
      exact hj
    · change ((Φ.getD e []).getD j (0, false)).1 = _
      rw [getD_eq_getElem' [] he, getD_eq_getElem' _ hj]

/-- «An occurrence lies in at most two tests. The total number of tests is the number of occurrences
minus the number of variables that occur, hence at most 3m − 1» (Section 6). -/
theorem stTests : StTests := by
  intro Φ hΦ hC
  have h3 : ∀ C ∈ Φ, C.length ≤ 3 := fun C h => (hC C h).2
  have inj2 : Function.Injective fun t : Slot 1 Φ.length 3 × Slot 1 Φ.length 3 => (occOfSlot t.1, occOfSlot t.2) := by
    rintro ⟨p, q⟩ ⟨p', q'⟩ h
    simp only [Prod.mk.injEq] at h
    rw [occOfSlot_injective h.1, occOfSlot_injective h.2]
  have hnd : (occAll Φ).Nodup := nodup_occIn h3 0 Φ.length
  have hsum : (tests Φ).length + ((occAll Φ).map fun o => (litOf Φ o).1).toFinset.card = (occAll Φ).length := by
    rw [← List.toFinset_card_of_nodup (nodup_tests h3), toFinset_tests h3, card_image_of_injective _ inj2, toFinset_vars,
      ← List.toFinset_card_of_nodup hnd, toFinset_occAll h3, card_image_of_injective _ occOfSlot_injective]
    exact card_testsOf_add h3 (by omega)
  refine ⟨fun o ho => ?_, hsum, ?_⟩
  · obtain ⟨p₀, rfl⟩ := exists_occOfSlot h3 ho
    rw [← List.toFinset_card_of_nodup ((nodup_tests h3).filter _)]
    refine (card_le_card (t := ({t ∈ testsOf Φ 1 Φ.length 3 | t.1 = p₀ ∨ t.2 = p₀} : Finset _).image fun t => (occOfSlot t.1, occOfSlot t.2)) ?_).trans (card_image_le.trans (card_tests_at_le_two p₀))
    intro x hx
    rw [List.mem_toFinset, List.mem_filter] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hx3 := List.mem_toFinset.2 hx1
    rw [toFinset_tests h3] at hx3
    obtain ⟨t, ht, rfl⟩ := mem_image.1 hx3
    simp only [Bool.or_eq_true, beq_iff_eq] at hx2
    exact mem_image.2 ⟨t, mem_filter.2 ⟨ht, hx2.imp (fun h => occOfSlot_injective h) fun h => occOfSlot_injective h⟩, rfl⟩
  · have h1 := length_occIn_le h3 0 Φ.length
    have h2 : 0 < ((occAll Φ).map fun o => (litOf Φ o).1).toFinset.card := by
      obtain ⟨C, Φ', rfl⟩ := List.exists_cons_of_ne_nil hΦ
      have h0 : ((0, 0) : ℕ × ℕ) ∈ occAll (C :: Φ') := mem_occAll.2 (List.length_pos_iff.2 (hC C List.mem_cons_self).1)
      exact card_pos.2 ⟨_, List.mem_toFinset.2 (List.mem_map_of_mem h0)⟩
    have h4 : (occAll Φ).length ≤ 3 * Φ.length := h1
    omega

end Coding
