/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-!
# One move of the play

Parties hold copies of units. A unit has two holders. The value of a position is the sum over all contents of
the copies (units that have not been seen are empty) of a joint weight, restricted to contents in which the two
copies of every current unit agree. A move takes some current units of two crossing bundles away and replaces the
condition that their copies agree by tables at the four parties and new units, summed over the outcomes.
-/

set_option linter.unusedSectionVars false

namespace Nc

open Finset

variable {F : Type*} [CommRing F] {A U W O : Type*} [Fintype A] [DecidableEq A] [Fintype U] [DecidableEq U]
  [Fintype W] [DecidableEq W] [Fintype O]

/-- The unit `id` is held by the party `a`. -/
def Holds (h0 h1 : U → A) (a : A) (id : U) : Prop := a = h0 id ∨ a = h1 id

instance (h0 h1 : U → A) (a : A) (id : U) : Decidable (Holds h0 h1 a id) := by
  unfold Holds; infer_instance

/-- The contents in which only seen units, at their holders, are not empty. -/
def Contents (h0 h1 : U → A) (e : W) (Seen : Finset U) : Finset (A → U → W) :=
  univ.filter fun y => ∀ a id, ¬ (id ∈ Seen ∧ Holds h0 h1 a id) → y a id = e

/-- The copies of all units in `Cur` agree. -/
def Agree (h0 h1 : U → A) (Cur : Finset U) (y : A → U → W) : Prop :=
  ∀ id ∈ Cur, y (h0 id) id = y (h1 id) id

instance (h0 h1 : U → A) (Cur : Finset U) (y : A → U → W) : Decidable (Agree h0 h1 Cur y) := by
  unfold Agree; infer_instance

/-- The value of a position. -/
def posVal (h0 h1 : U → A) (e : W) (Seen Cur : Finset U) (E : (A → U → W) → F) : F :=
  ∑ y ∈ Contents h0 h1 e Seen, if Agree h0 h1 Cur y then E y else 0

/-- Write common contents of the new units into the copies of their holders. -/
def ext (h0 h1 : U → A) (New : Finset U) (y : A → U → W) (z : U → W) : A → U → W := fun a id =>
  if id ∈ New ∧ Holds h0 h1 a id then z id else y a id

/-- Common contents of units: empty outside `New`. -/
def Common (e : W) (New : Finset U) : Finset (U → W) := univ.filter fun z => ∀ id, id ∉ New → z id = e

theorem ext_self {h0 h1 : U → A} {New : Finset U} {y : A → U → W} {z : U → W} {a : A} {id : U}
    (h : id ∈ New) (ha : Holds h0 h1 a id) : ext h0 h1 New y z a id = z id := by simp [ext, h, ha]

theorem ext_of_not {h0 h1 : U → A} {New : Finset U} {y : A → U → W} {z : U → W} {a : A} {id : U}
    (h : id ∉ New) : ext h0 h1 New y z a id = y a id := by simp [ext, h]

/-- Contents for `Seen ∪ New` whose copies of the new units agree = old contents and common contents. -/
theorem sum_contents_union (h0 h1 : U → A) (e : W) (Seen New : Finset U) (hd : Disjoint Seen New)
    (f : (A → U → W) → F) :
    (∑ y ∈ Contents h0 h1 e (Seen ∪ New), if Agree h0 h1 New y then f y else 0) =
      ∑ y ∈ Contents h0 h1 e Seen, ∑ z ∈ Common e New, f (ext h0 h1 New y z) := by
  rw [← Finset.sum_filter, ← Finset.sum_product']
  refine Finset.sum_bij'
    (i := fun y _ => (fun a id => if id ∈ New then e else y a id, fun id => if id ∈ New then y (h0 id) id else e))
    (j := fun p _ => ext h0 h1 New p.1 p.2) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Contents, Common, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_union] at hy ⊢
    refine ⟨fun a id hn => ?_, fun id hn => by simp [hn]⟩
    by_cases h : id ∈ New
    · simp [h]
    · simp only [h, if_false]
      apply hy.1
      rintro ⟨h1 | h1, h2⟩
      · exact hn ⟨h1, h2⟩
      · exact h h1
  · rintro ⟨y, z⟩ hp
    simp only [Contents, Common, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_union] at hp ⊢
    refine ⟨fun a id hn => ?_, fun id hid => ?_⟩
    · have h1 : ¬ (id ∈ New ∧ Holds h0 h1 a id) := fun h => hn ⟨Or.inr h.1, h.2⟩
      simp only [ext, h1, if_false]
      exact hp.1 a id fun h => hn ⟨Or.inl h.1, h.2⟩
    · rw [ext_self hid (Or.inl rfl), ext_self hid (Or.inr rfl)]
  · intro y hy
    simp only [Contents, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hy
    funext a id
    by_cases h : id ∈ New
    · by_cases ha : Holds h0 h1 a id
      · rw [ext_self h ha]
        simp only [h, if_true]
        rcases ha with rfl | rfl
        · rfl
        · exact hy.2 id h
      · simp only [ext, h, ha, and_false, if_false, if_true]
        exact (hy.1 a id fun hh => ha hh.2).symm
    · simp [ext, h]
  · rintro ⟨y, z⟩ hp
    simp only [Contents, Common, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and] at hp
    ext1
    · funext a id
      by_cases h : id ∈ New
      · simp only [h, if_true]
        exact (hp.1 a id fun hh => Finset.disjoint_left.1 hd hh.1 h).symm
      · simp [ext, h]
    · funext id
      by_cases h : id ∈ New
      · simp only [h, if_true]
        exact ext_self h (Or.inl rfl)
      · simp only [h, if_false]
        exact (hp.2 id h).symm
  · intro y hy
    simp only [Contents, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hy
    congr 1
    funext a id
    by_cases h : id ∈ New
    · by_cases ha : Holds h0 h1 a id
      · rw [ext_self h ha]
        simp only [h, if_true]
        rcases ha with rfl | rfl
        · rfl
        · exact (hy.2 id h).symm
      · simp only [ext, h, ha, and_false, if_false, if_true]
        exact hy.1 a id fun hh => ha hh.2
    · simp [ext, h]

end Nc
