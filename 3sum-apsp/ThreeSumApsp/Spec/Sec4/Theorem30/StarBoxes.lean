/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec4.Lemma29
public import ThreeSumApsp.Spec.Sec4.Theorem30.Cubes
public import ThreeSumApsp.Spec.Sec4.Theorem30.NineStrings

/-!
# The boxes with e stars, as a list (proof of Lemma 29)

"A box in which f of the symbols are P₀ or stars is obtained from a leaf of order m - f (namely the
leaf we get by replacing its stars with P₀) by turning the e lowest symbols P₀ of that leaf into
stars, for some e ≤ f."  So the boxes with exactly e stars are the leaves with between e and m - t
symbols P₀, with the first e digits 9 turned into 10: this is `starBoxes`.

The list contains exactly the boxes with e stars (`mem_starBoxes`, `exists_of_mem_starBoxes`), each
of them once (`starBoxes_nodup`), so it has as many members as there are such boxes
(`length_starBoxes`), and all lists together have as many members as there are boxes
(`sum_length_starBoxes`).

The lists are the order of work of Lemma 29: "We compute the values of the boxes in increasing order
of their number of stars", "Generating the boxes with e stars and inserting them into the trie".
All of them go into the trie of the tile.  The number of stars can be read off a box
(`starCount_of_mem_starBoxes`), so boxes from different lists are different strings, and a string
is a box exactly if it is in the list for its number of stars (`isBoxDigits_digitsC`).  There are
boxes with e stars only for e ≤ m - t (`le_of_mem_starBoxes`).  Replacing the highest star of a box
with e + 1 stars by a term gives a box with e stars (`exists_lastStar_of_mem_starBoxes`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-- The boxes with e stars, as lists of digits. -/
def starBoxes (L m t e : ℕ) : List (List ℕ) := (nineStrs L e (m - t)).map (starFirst e)

theorem length_starBoxes_eq_length_nineStrs (L m t e : ℕ) :
    (starBoxes L m t e).length = (nineStrs L e (m - t)).length :=
  List.length_map _

/-- Box number i comes from leaf number i. -/
theorem starFirst_mem_starBoxes {L m t e i : ℕ} (hi : i < (nineStrs L e (m - t)).length) :
    starFirst e (nineStrs L e (m - t))[i] ∈ starBoxes L m t e :=
  List.mem_map.2 ⟨_, List.getElem_mem hi, rfl⟩

/-- A member of the list comes from a leaf with between e and m - t symbols P₀. -/
private theorem exists_leaf_of_mem_starBoxes {L m t e : ℕ} {l : List ℕ}
    (h : l ∈ starBoxes L m t e) :
    ∃ τ : Leaf L, e ≤ (P0Levels τ).card ∧ (P0Levels τ).card ≤ m - t ∧
      digitsC (starLowest e τ) = l := by
  obtain ⟨l', hl', rfl⟩ := List.mem_map.1 h
  obtain ⟨hlen, hdig, hlo, hhi⟩ := (mem_nineStrs l').1 hl'
  obtain ⟨τ, rfl⟩ := exists_digitsT (L := L) l' hlen hdig
  exact ⟨τ, by rwa [card_P0Levels], by rwa [card_P0Levels], digitsC_starLowest e τ⟩

/-- The list contains exactly the boxes with e stars. -/
theorem mem_starBoxes {L : ℕ} (m t e : ℕ) (π : Cube L) :
    digitsC π ∈ starBoxes L m t e ↔ π ∈ boxesWithStars L m t e := by
  rw [mem_boxesWithStars]
  constructor
  · intro h
    obtain ⟨τ, hlo, hhi, hτ⟩ := exists_leaf_of_mem_starBoxes h
    obtain rfl : π = starLowest e τ := digitsC_injective L hτ.symm
    refine ⟨isBox_starLowest m t e τ hhi, ?_⟩
    rw [starLevels_starLowest, card_lowest]
    omega
  · rintro ⟨hbox, he⟩
    have hπ := eq_starLowest_starsToP0 π hbox.2
    have hcard := card_P0Levels_starsToP0 π
    rw [he] at hπ
    refine List.mem_map.2 ⟨digitsT (Cube.starsToP0 π),
      (mem_nineStrs _).2 ⟨length_digitsT _, digitsT_lt _, ?_, ?_⟩, ?_⟩
    · rw [← card_P0Levels]
      omega
    · rw [← card_P0Levels, hcard]
      exact hbox.1
    · rw [← digitsC_starLowest, ← hπ]

/-- Every member of the list is a cube. -/
theorem exists_of_mem_starBoxes {L m t e : ℕ} (l : List ℕ) (h : l ∈ starBoxes L m t e) :
    ∃ π : Cube L, digitsC π = l := by
  obtain ⟨τ, -, -, hτ⟩ := exists_leaf_of_mem_starBoxes h
  exact ⟨_, hτ⟩

/-- The number of stars can be read off a member of the list: the star is a symbol of its own, the
digit 10.  So boxes with different numbers of stars are different strings. -/
theorem starCount_of_mem_starBoxes {L m t e : ℕ} {l : List ℕ} (h : l ∈ starBoxes L m t e) :
    starCount l = e := by
  obtain ⟨π, rfl⟩ := exists_of_mem_starBoxes l h
  rw [← card_starLevels]
  exact (mem_boxesWithStars.1 ((mem_starBoxes m t e π).1 h)).2

/-- The string l is a box: it is in the list of the boxes with its number of stars. -/
abbrev IsBoxDigits (L m t : ℕ) (l : List ℕ) : Prop := l ∈ starBoxes L m t (starCount l)

theorem isBoxDigits_of_mem_starBoxes {L m t e : ℕ} {l : List ℕ} (h : l ∈ starBoxes L m t e) :
    IsBoxDigits L m t l := by
  rwa [IsBoxDigits, starCount_of_mem_starBoxes h]

/-- A string of symbols is in the list of the boxes with its number of stars exactly if it is a
box. -/
theorem isBoxDigits_digitsC {L : ℕ} (m t : ℕ) (π : Cube L) :
    IsBoxDigits L m t (digitsC π) ↔ π ∈ boxes L m t := by
  rw [IsBoxDigits, ← card_starLevels, mem_starBoxes, mem_boxesWithStars, mem_boxes]
  exact and_iff_left rfl

/-- There are boxes with e stars only for e ≤ m - t. -/
theorem le_of_mem_starBoxes {L m t e : ℕ} {l : List ℕ} (h : l ∈ starBoxes L m t e) : e ≤ m - t := by
  obtain ⟨τ, hlo, hhi, -⟩ := exists_leaf_of_mem_starBoxes h
  exact hlo.trans hhi

/-- The members of the lists are strings of L digits below 11. -/
theorem starBoxes_digits {L m t e : ℕ} {l : List ℕ} (h : l ∈ starBoxes L m t e) :
    l.length = L ∧ ∀ d ∈ l, d < 11 := by
  obtain ⟨π, rfl⟩ := exists_of_mem_starBoxes l h
  exact ⟨length_digitsC π, digitsC_lt π⟩

/-- Replacing the highest star of a box with e + 1 stars by a term gives a box with e stars (proof
of Lemma 29). -/
theorem exists_lastStar_of_mem_starBoxes {L m t e : ℕ} {l : List ℕ}
    (h : l ∈ starBoxes L m t (e + 1)) :
    ∃ p, lastStar l = some p ∧ ∀ d < 10, l.set p d ∈ starBoxes L m t e := by
  obtain ⟨π, rfl⟩ := exists_of_mem_starBoxes l h
  have hπ : π ∈ boxesWithStars L m t (e + 1) := (mem_starBoxes m t (e + 1) π).mp h
  have hcard : (Cube.starLevels π).card = e + 1 := (Finset.mem_filter.mp hπ).2
  have hne : (Cube.starLevels π).Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨_, lastStar_digitsC π hne, fun d hd => ?_⟩
  have hsplit := lemma_29_split hπ hne (termEquiv.symm ⟨d, hd⟩)
  rw [← mem_starBoxes, digitsC_replace] at hsplit
  have hidx : ((termIdx (termEquiv.symm ⟨d, hd⟩) : Fin 10) : ℕ) = d :=
    congrArg Fin.val (termEquiv.apply_symm_apply ⟨d, hd⟩)
  rwa [hidx] at hsplit

/-- No box occurs twice in the list: turning the stars back into nines gives the leaf. -/
theorem starBoxes_nodup (L m t e : ℕ) : (starBoxes L m t e).Nodup := by
  refine (nineStrs_nodup _ _ _).map_on fun x hx y hy h => ?_
  rw [← starsToNines_starFirst e (ten_notMem_of_mem_nineStrs hx), h,
    starsToNines_starFirst e (ten_notMem_of_mem_nineStrs hy)]

/-- The list has as many members as there are boxes with e stars. -/
theorem length_starBoxes (L m t e : ℕ) :
    (starBoxes L m t e).length = (boxesWithStars L m t e).card := by
  classical
  have himage : (boxesWithStars L m t e).image digitsC = (starBoxes L m t e).toFinset := by
    ext l
    rw [Finset.mem_image, List.mem_toFinset]
    constructor
    · rintro ⟨π, hπ, rfl⟩
      exact (mem_starBoxes m t e π).2 hπ
    · intro hl
      obtain ⟨π, rfl⟩ := exists_of_mem_starBoxes l hl
      exact ⟨π, (mem_starBoxes m t e π).1 hl, rfl⟩
  rw [← List.toFinset_card_of_nodup (starBoxes_nodup L m t e), ← himage,
    Finset.card_image_of_injective _ (digitsC_injective L)]

/-- All lists together have as many members as there are boxes (Lemma 29). -/
theorem sum_length_starBoxes (L m t : ℕ) :
    ((List.range (m - t + 1)).map fun e => (starBoxes L m t e).length).sum
      = (boxes L m t).card := by
  have hfibres : (boxes L m t).card = ∑ e ∈ Finset.range (m - t + 1),
      ((boxes L m t).filter fun π => (Cube.starLevels π).card = e).card := by
    refine Finset.card_eq_sum_card_fiberwise fun π hπ => ?_
    have := (mem_boxes.1 (Finset.mem_coe.1 hπ)).1
    simp only [Finset.coe_range, Set.mem_Iio]
    omega
  rw [List.sum_map_range, hfibres]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [length_starBoxes]
  refine congrArg Finset.card (Finset.ext fun π => ?_)
  rw [mem_boxesWithStars, Finset.mem_filter, mem_boxes]

end ThreeSumApsp.Spec
