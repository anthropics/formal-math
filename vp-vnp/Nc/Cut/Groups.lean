/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Cut.Play

/-!
# Groups of parties

The value of a position whose joint weight is a product of tables of the parties is a sum, over common contents of
the current units whose holders are in different groups, of products of values of the groups.
-/

set_option linter.unusedSectionVars false

namespace Nc

open Finset

variable {F : Type*} [CommRing F] {A U W G : Type*} [Fintype A] [DecidableEq A] [Fintype U] [DecidableEq U]
  [Fintype W] [DecidableEq W] [Fintype G] [DecidableEq G]

/-- The current units whose holders are in different groups. -/
def cutUnits (h0 h1 : U → A) (grp : A → G) (Cur : Finset U) : Finset U :=
  Cur.filter fun id => grp (h0 id) ≠ grp (h1 id)

/-- The contents of the copies held by the parties of the group `g`: only seen units, at their holders in `g`, are
not empty. -/
def GContents (h0 h1 : U → A) (e : W) (Seen : Finset U) (grp : A → G) (g : G) : Finset (A → U → W) :=
  univ.filter fun y => ∀ a id, ¬ (grp a = g ∧ id ∈ Seen ∧ Holds h0 h1 a id) → y a id = e

/-- The copies of current units agree if both holders are in the group `g`, and they are `b` if one is. -/
structure GAgree (h0 h1 : U → A) (grp : A → G) (g : G) (Cur : Finset U) (b : U → W) (y : A → U → W) : Prop where
  both : ∀ id ∈ Cur, grp (h0 id) = g → grp (h1 id) = g → y (h0 id) id = y (h1 id) id
  fst : ∀ id ∈ Cur, grp (h0 id) = g → grp (h1 id) ≠ g → y (h0 id) id = b id
  snd : ∀ id ∈ Cur, grp (h0 id) ≠ g → grp (h1 id) = g → y (h1 id) id = b id

theorem mem_contents_iff {h0 h1 : U → A} {e : W} {Seen : Finset U} {y : A → U → W} :
    y ∈ Contents h0 h1 e Seen ↔ ∀ a id, ¬ (id ∈ Seen ∧ Holds h0 h1 a id) → y a id = e := by
  simp [Contents]

theorem mem_common_iff {e : W} {New : Finset U} {z : U → W} :
    z ∈ Common e New ↔ ∀ id, id ∉ New → z id = e := by simp [Common]

theorem mem_gcontents_iff {h0 h1 : U → A} {e : W} {Seen : Finset U} {grp : A → G} {g : G} {y : A → U → W} :
    y ∈ GContents h0 h1 e Seen grp g ↔
      ∀ a id, ¬ (grp a = g ∧ id ∈ Seen ∧ Holds h0 h1 a id) → y a id = e := by
  simp [GContents]

open Classical in
/-- The value of the group `g` for the contents `b` of the units shared with other groups. -/
noncomputable def groupVal (h0 h1 : U → A) (e : W) (Seen Cur : Finset U) (grp : A → G) (φ : A → (U → W) → F)
    (g : G) (b : U → W) : F :=
  ∑ y ∈ GContents h0 h1 e Seen grp g, if GAgree h0 h1 grp g Cur b y then
    ∏ a ∈ univ.filter (fun a => grp a = g), φ a (y a) else 0

/-- **Groups.** -/
theorem posVal_groups (h0 h1 : U → A) (e : W) (Seen Cur : Finset U) (grp : A → G) (φ : A → (U → W) → F) :
    posVal h0 h1 e Seen Cur (fun y => ∏ a, φ a (y a)) =
      ∑ b ∈ Common e (cutUnits h0 h1 grp Cur), ∏ g, groupVal h0 h1 e Seen Cur grp φ g b := by
  classical
  have hR : ∀ b, (∏ g, groupVal h0 h1 e Seen Cur grp φ g b) =
      ∑ p ∈ Fintype.piFinset fun g => GContents h0 h1 e Seen grp g,
        if ∀ g, GAgree h0 h1 grp g Cur b (p g) then ∏ a, φ a (p (grp a) a) else 0 := by
    intro b
    simp only [groupVal]
    rw [Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.prod_ite_zero]
    simp only [Finset.mem_univ, true_imp_iff]
    congr 1
    rw [← Finset.prod_fiberwise univ grp]
    refine Finset.prod_congr rfl fun g _ => Finset.prod_congr rfl fun a ha => ?_
    rw [(Finset.mem_filter.1 ha).2]
  simp only [hR]
  rw [← Finset.sum_product', ← Finset.sum_filter, posVal, ← Finset.sum_filter]
  refine Finset.sum_bij'
    (i := fun y _ => (fun id => if id ∈ cutUnits h0 h1 grp Cur then y (h0 id) id else e,
      fun g a id => if grp a = g then y a id else e))
    (j := fun q _ => fun a id => q.2 (grp a) a id) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset, mem_contents_iff, mem_common_iff,
      mem_gcontents_iff] at hy ⊢
    refine ⟨⟨fun id hid => by simp [hid], fun g a id hn => ?_⟩, fun g => ⟨?_, ?_, ?_⟩⟩
    · by_cases h : grp a = g
      · simp only [h, if_true]
        exact hy.1 a id fun hh => hn ⟨h, hh⟩
      · simp [h]
    · intro id hid g1 g2
      simp [g1, g2, hy.2 id hid]
    · intro id hid g1 g2
      have : id ∈ cutUnits h0 h1 grp Cur := by
        simp only [cutUnits, Finset.mem_filter]
        exact ⟨hid, fun hh => g2 (hh ▸ g1)⟩
      simp [g1, this]
    · intro id hid g1 g2
      have : id ∈ cutUnits h0 h1 grp Cur := by
        simp only [cutUnits, Finset.mem_filter]
        exact ⟨hid, fun hh => g1 (hh ▸ g2)⟩
      simp [g2, this, hy.2 id hid]
  · rintro ⟨b, p⟩ hq
    simp only [Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset, mem_contents_iff, mem_common_iff,
      mem_gcontents_iff] at hq ⊢
    refine ⟨fun a id hn => hq.1.2 _ _ _ fun hh => hn hh.2, fun id hid => ?_⟩
    show p (grp (h0 id)) (h0 id) id = p (grp (h1 id)) (h1 id) id
    by_cases h : grp (h0 id) = grp (h1 id)
    · rw [h]
      exact (hq.2 (grp (h1 id))).both id hid h rfl
    · rw [(hq.2 _).fst id hid rfl (Ne.symm h), (hq.2 _).snd id hid h rfl]
  · intro y hy
    funext a id
    simp
  · rintro ⟨b, p⟩ hq
    simp only [Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset, mem_common_iff,
      mem_gcontents_iff] at hq ⊢
    ext1
    · funext id
      by_cases h : id ∈ cutUnits h0 h1 grp Cur
      · simp only [h, if_true]
        simp only [cutUnits, Finset.mem_filter] at h
        exact (hq.2 _).fst id h.1 rfl (Ne.symm h.2)
      · simp only [h, if_false]
        exact (hq.1.1 id h).symm
    · funext g a id
      by_cases h : grp a = g
      · subst h; simp
      · simp only [h, if_false]
        exact (hq.1.2 g a id fun hh => h hh.1).symm
  · intro y hy
    refine Finset.prod_congr rfl fun a _ => ?_
    simp

/-- **One move**, for contents at which the joint weight is not zero. -/
theorem posVal_move' {O : Type*} [Fintype O] (h0 h1 : U → A) (e : W) (Seen Cur Out : Finset U) (hOut : Out ⊆ Cur)
    (hCur : Cur ⊆ Seen) (New : O → Finset U) (hNew : ∀ o, Disjoint Seen (New o)) (E : (A → U → W) → F)
    (hE : ∀ o y z, E (ext h0 h1 (New o) y z) = E y) (C : O → (A → U → W) → F)
    (hC : ∀ y ∈ Contents h0 h1 e Seen, E y ≠ 0 → (if Agree h0 h1 Out y then (1 : F) else 0) =
      ∑ o, ∑ z ∈ Common e (New o), C o (ext h0 h1 (New o) y z)) :
    posVal h0 h1 e Seen Cur E =
      ∑ o, posVal h0 h1 e (Seen ∪ New o) ((Cur \ Out) ∪ New o) fun y => E y * C o y := by
  classical
  have h1' : ∀ o, posVal h0 h1 e (Seen ∪ New o) ((Cur \ Out) ∪ New o) (fun y => E y * C o y) =
      ∑ y ∈ Contents h0 h1 e Seen, if Agree h0 h1 (Cur \ Out) y then
        E y * ∑ z ∈ Common e (New o), C o (ext h0 h1 (New o) y z) else 0 := by
    intro o
    have e1 : ∀ y : A → U → W, (if Agree h0 h1 ((Cur \ Out) ∪ New o) y then E y * C o y else 0) =
        if Agree h0 h1 (New o) y then (if Agree h0 h1 (Cur \ Out) y then E y * C o y else 0) else 0 := by
      intro y
      have : Agree h0 h1 ((Cur \ Out) ∪ New o) y ↔ Agree h0 h1 (New o) y ∧ Agree h0 h1 (Cur \ Out) y := by
        simp only [Agree, Finset.mem_union]
        constructor
        · exact fun h => ⟨fun id hid => h id (Or.inr hid), fun id hid => h id (Or.inl hid)⟩
        · rintro ⟨ha, hb⟩ id (hid | hid)
          · exact hb id hid
          · exact ha id hid
      by_cases ha : Agree h0 h1 (New o) y <;> by_cases hb : Agree h0 h1 (Cur \ Out) y <;>
        simp [this, ha, hb]
    rw [posVal, Finset.sum_congr rfl fun y _ => e1 y, sum_contents_union h0 h1 e Seen (New o) (hNew o)]
    refine Finset.sum_congr rfl fun y _ => ?_
    have hne : ∀ id, id ∈ Seen → id ∉ New o := fun id h => Finset.disjoint_left.1 (hNew o) h
    have e2 : ∀ z, Agree h0 h1 (Cur \ Out) (ext h0 h1 (New o) y z) ↔ Agree h0 h1 (Cur \ Out) y := by
      intro z
      simp only [Agree]
      refine forall₂_congr fun id hid => ?_
      have := hne id (hCur (Finset.mem_sdiff.1 hid).1)
      rw [ext_of_not this, ext_of_not this]
    have e3 : ∀ z, E (ext h0 h1 (New o) y z) = E y := fun z => hE o y z
    simp only [e2, e3]
    split_ifs
    · rw [Finset.mul_sum]
    · simp
  simp only [h1']
  rw [Finset.sum_comm, posVal]
  refine Finset.sum_congr rfl fun y hy => ?_
  by_cases hE0 : E y = 0
  · simp [hE0]
  by_cases hb : Agree h0 h1 (Cur \ Out) y
  · simp only [hb, if_true]
    rw [← Finset.mul_sum, ← hC y hy hE0]
    have : Agree h0 h1 Cur y ↔ Agree h0 h1 Out y := by
      constructor
      · exact fun h id hid => h id (hOut hid)
      · intro h id hid
        by_cases ho : id ∈ Out
        · exact h id ho
        · exact hb id (Finset.mem_sdiff.2 ⟨hid, ho⟩)
    by_cases ho : Agree h0 h1 Out y <;> simp [this, ho]
  · have : ¬ Agree h0 h1 Cur y := fun h => hb fun id hid => h id (Finset.mem_sdiff.1 hid).1
    simp [hb, this]

end Nc
