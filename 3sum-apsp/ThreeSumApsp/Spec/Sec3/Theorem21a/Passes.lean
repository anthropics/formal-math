/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Util.List

/-!
# One pass over a list

The routines of the reduction after Chan and He ([CH20, Theorem 5.1], one of the reductions behind
Theorem 21(a)) run through arrays from left to right.  This file says what two kinds of
passes have written after the first `i` elements, and how one more element changes it.

* A filter pass selects elements and writes a function of them: `passList`, with one lemma for an
  element that is selected (`passList_succ_of`) and one for an element that is not
  (`passList_succ_of_not`).
* A pass over a sorted list writes the distinct values and their multiplicities.  `DistSt L D i`
  says that `D` is the list of the distinct values among the first `i` elements, and `countTo L i`
  counts occurrences among them.  An element either opens a new value (`DistSt.opens`,
  `map_countTo_opens`) or repeats the last one (`DistSt.bumps`, `map_countTo_bumps`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## A filter pass -/

section Filter

variable {α β : Type}

/-- What a filter pass has written after it has seen the first `i` elements. -/
def passList (p : α → Bool) (f : α → β) (Z : List α) (i : ℕ) : List β := ((Z.take i).filter p).map f

/-- At the start nothing is written. -/
@[simp] theorem passList_zero (p : α → Bool) (f : α → β) (Z : List α) : passList p f Z 0 = [] := by
  simp [passList]

/-- At the end all the selected elements are written. -/
theorem passList_length (p : α → Bool) (f : α → β) (Z : List α) :
    passList p f Z Z.length = (Z.filter p).map f := by
  simp [passList]

/-- An element that is selected is written. -/
theorem passList_succ_of {p : α → Bool} (f : α → β) {Z : List α} {i : ℕ} (hi : i < Z.length)
    (h : p Z[i] = true) : passList p f Z (i + 1) = passList p f Z i ++ [f Z[i]] := by
  unfold passList
  rw [List.take_add_one, List.getElem?_eq_getElem hi, List.filter_append, List.map_append]
  simp [h]

/-- An element that is not selected changes nothing. -/
theorem passList_succ_of_not {p : α → Bool} (f : α → β) {Z : List α} {i : ℕ} (hi : i < Z.length)
    (h : p Z[i] = false) : passList p f Z (i + 1) = passList p f Z i := by
  unfold passList
  rw [List.take_add_one, List.getElem?_eq_getElem hi, List.filter_append, List.map_append]
  simp [h]

/-- After `i` elements at most `i` are written. -/
theorem length_passList_le (p : α → Bool) (f : α → β) (Z : List α) (i : ℕ) :
    (passList p f Z i).length ≤ i := by
  rw [passList, List.length_map]
  exact (List.length_filter_le _ _).trans (List.length_take_le i Z)

end Filter

/-! ## The distinct values of a sorted list -/

/-- How often `x` occurs among the first `i` elements. -/
def countTo (L : List ℤ) (i : ℕ) (x : ℤ) : ℤ := ((L.take i).count x : ℤ)

/-- One more element in the count. -/
theorem countTo_succ (L : List ℤ) {i : ℕ} (hi : i < L.length) (x : ℤ) :
    countTo L (i + 1) x = countTo L i x + if x = L.getD i 0 then 1 else 0 := by
  rw [countTo, countTo, List.count_take_succ_getD L x hi 0, Nat.cast_add, Nat.cast_ite,
    Nat.cast_one,
    Nat.cast_zero]
  exact congrArg _ (if_congr eq_comm rfl rfl)

/-- A count is not negative. -/
theorem countTo_nonneg (L : List ℤ) (i : ℕ) (x : ℤ) : 0 ≤ countTo L i x := Int.natCast_nonneg _

/-- Among `i` elements a value occurs at most `i` times. -/
theorem countTo_le (L : List ℤ) (i : ℕ) (x : ℤ) : countTo L i x ≤ i :=
  Int.ofNat_le.2 (List.count_le_length.trans (List.length_take_le i L))

/-- `D` is the list of the distinct values among the first `i` elements of `L`, and it ends with
the last of them. -/
structure DistSt (L D : List ℤ) (i : ℕ) : Prop where
  nodup : D.Nodup
  mem : ∀ x, x ∈ D ↔ x ∈ L.take i
  le : D.length ≤ i
  last : 0 < i → 0 < D.length ∧ D.getD (D.length - 1) 0 = L.getD (i - 1) 0

/-- At the start there are no values. -/
theorem DistSt.zero (L : List ℤ) : DistSt L [] 0 :=
  ⟨List.nodup_nil, by simp, le_rfl, fun h => absurd h (by omega)⟩

/-- If element `i` of a sorted list differs from the last value written, or nothing is written yet,
then it has not occurred before, and appending it gives the distinct values among the first `i + 1`
elements. -/
theorem DistSt.opens {L D : List ℤ} {i : ℕ} (h : DistSt L D i) (hs : L.Pairwise (· ≤ ·))
    (hi : i < L.length) (hne : D.length = 0 ∨ L.getD i 0 ≠ D.getD (D.length - 1) 0) :
    DistSt L (D ++ [L.getD i 0]) (i + 1) ∧ L.getD i 0 ∉ L.take i := by
  have hnot : L.getD i 0 ∉ L.take i := by
    refine List.getD_notMem_take_of_sorted hs hi 0 ?_
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · exact Or.inl h0
    · obtain ⟨hpos, hlast⟩ := h.last h0
      exact Or.inr (hlast ▸ hne.resolve_left (by omega))
  refine ⟨⟨?_, fun x => ?_, ?_, fun _ => by simp⟩, hnot⟩
  · -- no value twice
    exact List.nodup_append.2 ⟨h.nodup, List.nodup_singleton _, fun a ha b hb e =>
      hnot ((h.mem _).1 (List.mem_singleton.1 hb ▸ e ▸ ha))⟩
  · -- the values are the elements seen
    rw [List.take_succ_getD L hi 0, List.mem_append, List.mem_append, h.mem]
  · -- at most one value for each element
    rw [List.length_append, List.length_singleton]
    exact Nat.succ_le_succ h.le

/-- If element `i` equals the last value written, then the distinct values among the first `i + 1`
elements are those among the first `i`. -/
theorem DistSt.bumps {L D : List ℤ} {i : ℕ} (h : DistSt L D i) (hi : i < L.length)
    (hpos : 0 < D.length) (he : L.getD i 0 = D.getD (D.length - 1) 0) : DistSt L D (i + 1) := by
  refine ⟨h.nodup, fun x => ?_, h.le.trans (Nat.le_succ i), fun _ => ⟨hpos, by simpa using he.symm⟩⟩
  rw [List.take_succ_getD L hi 0, List.mem_append, ← h.mem, List.mem_singleton]
  refine ⟨Or.inl, ?_⟩
  rintro (hx | rfl)
  · exact hx
  · rw [he, List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _

/-- The multiplicities after a new value: the old ones, and a 1 at the end. -/
theorem map_countTo_opens {L D : List ℤ} {i : ℕ} (h : DistSt L D i) (hi : i < L.length)
    (hnot : L.getD i 0 ∉ L.take i) :
    (D ++ [L.getD i 0]).map (countTo L (i + 1)) = D.map (countTo L i) ++ [1] := by
  rw [List.map_append, List.map_singleton]
  congr 1
  · refine List.map_congr_left fun x hx => ?_
    rw [countTo_succ L hi, if_neg, add_zero]
    rintro rfl
    exact hnot ((h.mem _).1 hx)
  · rw [countTo_succ L hi, if_pos rfl, countTo, List.count_eq_zero_of_not_mem hnot]
    rfl

/-- The multiplicities after a repeated value: the last one goes up by one. -/
theorem map_countTo_bumps {L D : List ℤ} {i : ℕ} (h : DistSt L D i) (hi : i < L.length)
    (hpos : 0 < D.length) (he : L.getD i 0 = D.getD (D.length - 1) 0) :
    D.map (countTo L (i + 1)) =
      (D.map (countTo L i)).set (D.length - 1) (countTo L i (D.getD (D.length - 1) 0) + 1) := by
  refine List.ext_getElem (by simp) fun j hj _ => ?_
  rw [List.length_map] at hj
  have hlast : D.getD (D.length - 1) 0 = D[D.length - 1] := List.getD_eq_getElem _ _ _
  rw [List.getElem_map, countTo_succ L hi, he]
  by_cases hc : j = D.length - 1
  · subst hc
    rw [List.getElem_set_self, if_pos hlast.symm, hlast]
  · rw [List.getElem_set_of_ne (by omega), List.getElem_map, if_neg, add_zero]
    exact fun e => hc ((List.Nodup.getElem_inj_iff h.nodup).1 (e.trans hlast))

end ThreeSumApsp.Spec
