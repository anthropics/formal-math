/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Coding.OccLinks
import all StepMachines.Prog.CountNet
import Eight.ViaGrouping.SatPsi
import Mathlib.Tactic.Ring

/-! # Lean's network of Φ is the printed one with padding

Section 6: «A setting z_a of node a is a bit string with one bit z_a[o] for each occurrence o in
cluster a, and S_a is the set of all these bit strings.» `stOccNet` proves the seven fields of
`Coding.PaddingOf (occNet g Φ) (satNet g 3 Φ) (padOcc g Φ)`:
* the padded string has the bit z_a[o] at the place of o in its cluster (`getD_padOcc_occ`), so
  padding is one to one;
* a string of 3·m̄ bits with 0 at the places without a literal is a padded setting
  (`exists_padOcc`), and elsewhere Lean's W_a is 0;
* Lean's W_a at a padded setting is the printed W_a: «every clause of cluster a has a true
  occurrence» (`clause_iff`) and «z_a[o] = z_a[o'] for every test {o,o'} with both occurrences in
  cluster a» (`inside_iff`);
* z_a|_b is the same string in both networks (`restr_padOcc`), so Ψ_{a,b} = [z_a|_b = z_b|_a] and
  f_{a,b} = [z_a|_b = θ] agree; that Lean's Ψ and f have this form is `Eight.ViaGrouping.satPsi_eq`
  and `satF_eq` (proof/networks/Eight/ViaGrouping/SatPsi.lean).
  `import all StepMachines.Prog.CountNet` gives access to `locals_eq`, `rows_eq` and `boole_congr`,
  which are not public. -/

public section

namespace Coding

open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight.SecNetworks Eight.ViaGrouping

variable {g : ℕ} {Φ : Fml}

/-! ### The padded string -/

/-- A padded setting has 3·m̄ bits. -/
theorem length_padOcc (a : Fin g) (z : List Bool) : (padOcc g Φ a z).length = mu g Φ * 3 := by simp [padOcc]

/-- The bit of the padded string at place i of the cluster. -/
theorem getD_padOcc (a : Fin g) (z : List Bool) {i : ℕ} (hi : i < mu g Φ * 3) :
    (padOcc g Φ a z).getD i false = (decide (i % 3 < (Φ.getD (a.val * mu g Φ + i / 3) []).length) && bitAt g Φ a.val z (a.val * mu g Φ + i / 3, i % 3)) := by
  rw [padOcc, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

/-- The place of an occurrence of cluster a within the cluster. -/
theorem place_sub {a e j : ℕ} (h : a * mu g Φ ≤ e) : place (e, j) - a * (mu g Φ * 3) = (e - a * mu g Φ) * 3 + j := by
  have e1 : a * (mu g Φ * 3) = a * mu g Φ * 3 := by ring
  rw [e1]
  simp only [place]
  omega

/-- The padded string has the bit z_a[o] at the place of the occurrence o. -/
theorem getD_padOcc_occ (h3 : ∀ C ∈ Φ, C.length ≤ 3) (a : Fin g) (z : List Bool) {o : ℕ × ℕ} (ho : o ∈ occOf g Φ a.val) :
    (padOcc g Φ a z).getD (place o - a.val * (mu g Φ * 3)) false = bitAt g Φ a.val z o := by
  obtain ⟨e, j⟩ := o
  have hm := mem_occIn.1 ho
  have h1 : a.val * mu g Φ ≤ e := hm.1
  have h2 : e < a.val * mu g Φ + mu g Φ := hm.2.1
  have h4 : j < (Φ.getD e []).length := hm.2.2
  have h5 := length_getD_le h3 e
  have e1 : ((e - a.val * mu g Φ) * 3 + j) / 3 = e - a.val * mu g Φ := by omega
  have e2 : ((e - a.val * mu g Φ) * 3 + j) % 3 = j := by omega
  have e3 : a.val * mu g Φ + (e - a.val * mu g Φ) = e := by omega
  rw [place_sub h1, getD_padOcc a z (by omega), e1, e2, e3, decide_eq_true h4, Bool.true_and]

/-- A list of values, read at the position of a member. -/
theorem getD_map_idxOf {α : Type} [BEq α] [LawfulBEq α] (f : α → Bool) {l : List α} {x : α} (hx : x ∈ l) : (l.map f).getD (l.idxOf x) false = f x := by
  have h := List.idxOf_lt_length_of_mem hx
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h, List.getElem_idxOf h]
  rfl

/-- What stands at place r of cluster a. -/
theorem litAt_local (a r : ℕ) : litAt 3 Φ (a * (mu g Φ * 3) + r) = if r % 3 < (Φ.getD (a * mu g Φ + r / 3) []).length then some (litOf Φ (a * mu g Φ + r / 3, r % 3)) else none := by
  have e : a * (mu g Φ * 3) = a * mu g Φ * 3 := by ring
  have e1 : (a * mu g Φ * 3 + r) / 3 = a * mu g Φ + r / 3 := by omega
  have e2 : (a * mu g Φ * 3 + r) % 3 = r % 3 := by omega
  rw [litAt_eq, e, e1, e2]

/-- A padded setting has 0 at the places without a literal. -/
theorem zero_padOcc (hg : 0 < g) (a : Fin g) (z : List Bool) :
    ((locals g 3 Φ).all fun r => (litAt 3 Φ (a.val * (mu g Φ * 3) + r)).isSome || !((padOcc g Φ a z).getD r false)) = true := by
  rw [locals_eq hg, List.all_eq_true]
  intro r hr
  rw [getD_padOcc a z (List.mem_range.1 hr), litAt_local]
  by_cases h : r % 3 < (Φ.getD (a.val * mu g Φ + r / 3) []).length
  · rw [if_pos h]; rfl
  · rw [if_neg h, decide_eq_false h]; rfl

/-- A string of 3·m̄ bits with 0 at the places without a literal is a padded setting. -/
theorem exists_padOcc (hg : 0 < g) (a : Fin g) {y : List Bool} (hy : y.length = mu g Φ * 3)
    (h0 : ((locals g 3 Φ).all fun r => (litAt 3 Φ (a.val * (mu g Φ * 3) + r)).isSome || !(y.getD r false)) = true) :
    ∃ z : List Bool, z.length = (occOf g Φ a.val).length ∧ padOcc g Φ a z = y := by
  refine ⟨(occOf g Φ a.val).map fun o => y.getD (place o - a.val * (mu g Φ * 3)) false, List.length_map _, ext_getD ((length_padOcc a _).trans hy.symm) fun i hi => ?_⟩
  rw [length_padOcc] at hi
  rw [getD_padOcc a _ hi]
  by_cases h : i % 3 < (Φ.getD (a.val * mu g Φ + i / 3) []).length
  · have ho : (a.val * mu g Φ + i / 3, i % 3) ∈ occOf g Φ a.val := mem_occIn.2 ⟨Nat.le_add_right _ _, by change a.val * mu g Φ + i / 3 < _; omega, h⟩
    rw [decide_eq_true h, Bool.true_and, bitAt, getD_map_idxOf _ ho, place_sub (Nat.le_add_right _ _)]
    congr 1
    omega
  · rw [locals_eq hg, List.all_eq_true] at h0
    have h1 := h0 i (List.mem_range.2 hi)
    rw [litAt_local, if_neg h] at h1
    rw [decide_eq_false h, Bool.false_and]
    cases hb : y.getD i false with
    | false => rfl
    | true =>
      rw [hb] at h1
      exact absurd h1 (by decide)

/-- Padding is one to one. -/
theorem padOcc_inj (h3 : ∀ C ∈ Φ, C.length ≤ 3) (a : Fin g) {z z' : List Bool} (hz : z.length = (occOf g Φ a.val).length) (hz' : z'.length = (occOf g Φ a.val).length)
    (h : padOcc g Φ a z = padOcc g Φ a z') : z = z' := by
  refine ext_getD (hz.trans hz'.symm) fun t ht => ?_
  rw [hz] at ht
  have ho := List.getElem_mem ht
  have h1 := getD_padOcc_occ h3 a z ho
  rw [h, getD_padOcc_occ h3 a z' ho] at h1
  unfold bitAt at h1
  have hnd : (occOf g Φ a.val).Nodup := nodup_occIn h3 _ _
  rw [hnd.idxOf_getElem t ht] at h1
  exact h1.symm

/-! ### W -/

/-- «every clause of cluster a has a true occurrence», for one clause: Lean's condition at a padded
setting is the printed one. -/
theorem clause_iff (h3 : ∀ C ∈ Φ, C.length ≤ 3) (a : Fin g) (z : List Bool) {c : ℕ} (hc : c < mu g Φ) :
    ((List.range 3).any fun j => (litAt 3 Φ ((a.val * mu g Φ + c) * 3 + j)).map Prod.snd == some ((padOcc g Φ a z).getD (c * 3 + j) false)) = true ↔
      ((List.range (Φ.getD (a.val * mu g Φ + c) []).length).any fun j => isTrue g Φ a.val z (a.val * mu g Φ + c, j)) = true := by
  have h5 := length_getD_le h3 (a.val * mu g Φ + c)
  have key : ∀ j < 3, ((litAt 3 Φ ((a.val * mu g Φ + c) * 3 + j)).map Prod.snd = some ((padOcc g Φ a z).getD (c * 3 + j) false) ↔
      j < (Φ.getD (a.val * mu g Φ + c) []).length ∧ isTrue g Φ a.val z (a.val * mu g Φ + c, j) = true) := by
    intro j hj
    have e1 : ((a.val * mu g Φ + c) * 3 + j) / 3 = a.val * mu g Φ + c := by omega
    have e2 : ((a.val * mu g Φ + c) * 3 + j) % 3 = j := by omega
    have e3 : (c * 3 + j) / 3 = c := by omega
    have e4 : (c * 3 + j) % 3 = j := by omega
    rw [litAt_eq, e1, e2, getD_padOcc a z (by omega), e3, e4]
    by_cases h : j < (Φ.getD (a.val * mu g Φ + c) []).length
    · rw [if_pos h, decide_eq_true h, Bool.true_and, Option.map_some, Option.some.injEq]
      unfold isTrue
      rw [beq_iff_eq]
      exact ⟨fun e => ⟨h, e.symm⟩, fun e => e.2.symm⟩
    · rw [if_neg h]
      exact ⟨fun e => by simp at e, fun e => absurd e.1 h⟩
  simp only [List.any_eq_true, List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨j, hj, h⟩
    exact ⟨j, (key j hj).1 h⟩
  · rintro ⟨j, hj, h⟩
    exact ⟨j, by omega, (key j (by omega)).2 ⟨hj, h⟩⟩

/-- «every clause of cluster a has a true occurrence»: Lean's condition at a padded setting is the
printed one. -/
theorem clauses_iff (hg : 0 < g) (h3 : ∀ C ∈ Φ, C.length ≤ 3) (a : Fin g) (z : List Bool) :
    ((rows g Φ).all fun c => !(decide (a.val * mu g Φ + c < Φ.length)) ||
        (List.range 3).any fun j => (litAt 3 Φ ((a.val * mu g Φ + c) * 3 + j)).map Prod.snd == some ((padOcc g Φ a z).getD (c * 3 + j) false)) = true ↔
      ((List.range' (a.val * mu g Φ) (mu g Φ)).all fun e => !(decide (e < Φ.length)) || (List.range (Φ.getD e []).length).any fun j => isTrue g Φ a.val z (e, j)) = true := by
  rw [rows_eq hg]
  simp only [List.all_eq_true, List.mem_range, List.mem_range'_1, Bool.or_eq_true]
  constructor
  · rintro H e ⟨h1, h2⟩
    have h := H (e - a.val * mu g Φ) (by omega)
    rw [clause_iff h3 a z (by omega), Nat.add_sub_cancel' h1] at h
    exact h
  · intro H c hc
    rw [clause_iff h3 a z hc]
    exact H _ ⟨Nat.le_add_right _ _, by omega⟩

/-- «z_a[o] = z_a[o'] for every test {o,o'} with both occurrences in cluster a»: Lean's condition at
a padded setting is the printed one. -/
theorem inside_iff (hg : 0 < g) (h3 : ∀ C ∈ Φ, C.length ≤ 3) (a : Fin g) (z : List Bool) :
    ((links g 3 Φ a.val a.val).all fun p => (padOcc g Φ a z).getD p.1 false == (padOcc g Φ a z).getD p.2 false) = true ↔
      ((testsBetween g Φ a.val a.val).all fun p => bitAt g Φ a.val z p.1 == bitAt g Φ a.val z p.2) = true := by
  have e := map_links hg h3 (le_refl a.val) (Φ := Φ) fun q => (padOcc g Φ a z).getD (q.1 - a.val * (mu g Φ * 3)) false == (padOcc g Φ a z).getD (q.2 - a.val * (mu g Φ * 3)) false
  simp only [Nat.add_sub_cancel_left] at e
  have e2 := congrArg (fun l : List Bool => l.all id) e
  simp only [List.all_map, Function.comp_def, id] at e2
  rw [e2]
  simp only [List.all_eq_true]
  refine forall₂_congr fun p hp => ?_
  obtain ⟨ht, c1, c2⟩ := (mem_testsBetween h3 (le_refl a.val)).1 hp
  obtain ⟨ho, ho', -⟩ := (mem_tests_iff h3 (o := p.1) (o' := p.2)).1 ht
  rw [getD_padOcc_occ h3 a z ((mem_occOf_iff hg).2 ⟨ho, c1⟩), getD_padOcc_occ h3 a z ((mem_occOf_iff hg).2 ⟨ho', c2⟩)]

/-! ### z_a|_b -/

/-- z_a|_b is the same string in both networks: «let z_a|_b ∈ {0,1}^{c_{a,b}} list the bits of z_a
at their occurrences in cluster a» (Section 6). -/
theorem restr_padOcc (hg : 0 < g) (h3 : ∀ C ∈ Φ, C.length ≤ 3) {a b : Fin g} (hab : a ≠ b) (z : List Bool) : restr g 3 Φ a.val b.val (padOcc g Φ a z) = restrict g Φ a.val b.val z := by
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with h | h
  · have e := map_links hg h3 h.le (Φ := Φ) fun q => (padOcc g Φ a z).getD (q.1 - a.val * (mu g Φ * 3)) false
    simp only [Nat.add_sub_cancel_left] at e
    rw [restr_of_lt h, e, restrict]
    refine List.map_congr_left fun p hp => ?_
    obtain ⟨ht, c1, -⟩ := (mem_testsBetween h3 h.le).1 hp
    obtain ⟨ho, -, -⟩ := (mem_tests_iff h3 (o := p.1) (o' := p.2)).1 ht
    rw [if_pos c1, getD_padOcc_occ h3 a z ((mem_occOf_iff hg).2 ⟨ho, c1⟩)]
  · have e := map_links hg h3 h.le (Φ := Φ) fun q => (padOcc g Φ a z).getD (q.2 - a.val * (mu g Φ * 3)) false
    simp only [Nat.add_sub_cancel_left] at e
    rw [restr_of_gt h, e, restrict, testsBetween_comm a.val b.val]
    refine List.map_congr_left fun p hp => ?_
    obtain ⟨ht, c1, c2⟩ := (mem_testsBetween h3 h.le).1 hp
    obtain ⟨-, ho', -⟩ := (mem_tests_iff h3 (o := p.1) (o' := p.2)).1 ht
    rw [if_neg (by omega), getD_padOcc_occ h3 a z ((mem_occOf_iff hg).2 ⟨ho', c2⟩)]

/-! ### The seven fields -/

/-- **Lean's network of Φ is the printed one with padding**: «A setting z_a of node a is a bit
string with one bit z_a[o] for each occurrence o in cluster a, and S_a is the set of all these bit
strings» (Section 6), where Lean's settings have one bit for each of the 3·m̄ places of a cluster. -/
theorem stOccNet : StOccNet := by
  intro g Φ hg h3
  refine ⟨fun a z _ => ?_, fun a z hz z' hz' h => ?_, fun a y hy hno => ?_, fun a z _ => ?_, fun a b hab z _ z' _ => ?_, fun a b _ => ?_, fun a b hab z _ θ hθ => ?_⟩
  · exact mem_words.2 (length_padOcc a z)
  · exact padOcc_inj h3 a (mem_words.1 hz) (mem_words.1 hz') h
  · change wF g 3 (Φ, (a.val, y)) = 0
    unfold wF
    rw [if_neg]
    intro hc
    simp only [Bool.and_eq_true] at hc
    obtain ⟨z, hz, hzy⟩ := exists_padOcc hg a (mem_words.1 hy) hc.1.1
    exact hno z (mem_words.2 hz) hzy
  · change wF g 3 (Φ, (a.val, padOcc g Φ a z)) = _
    unfold wF occNet
    refine boole_congr ?_
    simp only [Bool.and_eq_true]
    exact ⟨fun h => ⟨(clauses_iff hg h3 a z).1 h.1.2, (inside_iff hg h3 a z).1 h.2⟩, fun h => ⟨⟨zero_padOcc hg a z, (clauses_iff hg h3 a z).2 h.1⟩, (inside_iff hg h3 a z).2 h.2⟩⟩
  · change (wordNet g 3 Φ).Ψ a b (padOcc g Φ a z) (padOcc g Φ b z') = if restrict g Φ a.val b.val z = restrict g Φ b.val a.val z' then 1 else 0
    rw [← satPsi_eq hab, satPsi]
    change (if restr g 3 Φ a.val b.val (padOcc g Φ a z) = restr g 3 Φ b.val a.val (padOcc g Φ b z') then (1 : ℤ) else 0) = _
    rw [restr_padOcc hg h3 hab, restr_padOcc hg h3 hab.symm]
  · exact capF_eq hg h3 a.val b.val
  · change fF g 3 (Φ, ((a.val, b.val), (padOcc g Φ a z, θ))) = if restrict g Φ a.val b.val z = θ then 1 else 0
    rw [satF_eq a.val b.val _ ((mem_words.1 hθ).trans (capF_eq hg h3 a.val b.val).symm), restr_padOcc hg h3 hab]

end Coding
