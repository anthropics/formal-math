/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GeneralPieces.Ring.Basic
public import GeneralPieces.Ring.Bridge
public import Mathlib.Combinatorics.Colex
public import Mathlib.Data.List.Lex

/-! # The number h and the lexicographic list of the partitions of h

The first sentence of the proof of the theorem on the pieces with ρ = 1/√2 in Appendix B: "Given λ ≥
1, let h ≥ 2 be the least integer with p(h) ≥ 2^λ, and let μ(x) be the partition of h with
number x ∈ {0,1}^λ (read as an integer, counting from 0) in the lexicographic list of the partitions
of h, written as nonincreasing sequences."
Proved here: such an h exists (`hOfSpec`), and it equals the h defined by `ClauseBound.Part.hOf`
(`hOf_eq`); different partitions of h have different numbers in the list, and every j < p(h)
is the number of a partition of h (`lexNum_injOn`, `exists_lexNum_eq`); a string read as an integer
is below 2^λ, and different strings give different integers (`val_lt`, `val_injective`); so for 2^λ
≤ p(h) there
is exactly one function μ as in that sentence, and it is injective (`existsUnique_isMu`,
`IsMu.injective`). -/

public section

namespace GeneralPieces.Lex

open AppHalfPieces Finset

/-! ### The number h -/

/-- The h of the appendix equals the h defined by `ClauseBound.Part.hOf`. -/
theorem hOf_eq (lam : ℕ) : AppHalfPieces.hOf lam = ClauseBound.Part.hOf lam := by
  have hne : {h | 2 ≤ h ∧ 2 ^ lam ≤ Partitions.p h}.Nonempty := ClauseBound.Part.exists_h lam
  refine le_antisymm (Nat.sInf_le ⟨ClauseBound.Part.two_le_hOf lam, ClauseBound.Part.two_pow_le_p_hOf lam⟩) ?_
  unfold ClauseBound.Part.hOf
  exact Nat.find_min' _ (Nat.sInf_mem hne)

/-! ### The number of an element in a sorted list -/

section Rank

variable {α β : Type} [LinearOrder β] [DecidableRel fun a b : β => a < b] (S : Finset α) (f : α → β)

/-- If f(a) < f(b) and a is in the list, fewer elements come before a than before b. -/
theorem rank_lt {a b : α} (ha : a ∈ S) (hab : f a < f b) : #{c ∈ S | f c < f a} < #{c ∈ S | f c < f b} := by
  refine card_lt_card ⟨fun c hc => ?_, fun hsub => ?_⟩
  · exact mem_filter.2 ⟨(mem_filter.1 hc).1, (mem_filter.1 hc).2.trans hab⟩
  · exact lt_irrefl _ (mem_filter.1 (hsub (mem_filter.2 ⟨ha, hab⟩))).2

/-- The number of an element of the list is below the length of the list. -/
theorem rank_lt_card {a : α} (ha : a ∈ S) : #{c ∈ S | f c < f a} < #S :=
  card_lt_card ⟨filter_subset _ _, fun hsub => lt_irrefl _ (mem_filter.1 (hsub ha)).2⟩

/-- Different elements of the list have different numbers. -/
theorem rank_injOn (hf : Set.InjOn f S) : Set.InjOn (fun a => #{c ∈ S | f c < f a}) S := by
  intro a ha b hb hab
  rcases lt_trichotomy (f a) (f b) with h | h | h
  · exact absurd hab (rank_lt S f ha h).ne
  · exact hf ha hb h
  · exact absurd hab (rank_lt S f hb h).ne'

/-- Every number below the length of the list is the number of an element. -/
theorem exists_rank_eq (hf : Set.InjOn f S) {j : ℕ} (hj : j < #S) : ∃ a ∈ S, #{c ∈ S | f c < f a} = j := by
  have h1 : S.image (fun a => #{c ∈ S | f c < f a}) = range #S := by
    refine eq_of_subset_of_card_le (fun i hi => ?_) ?_
    · obtain ⟨a, ha, rfl⟩ := mem_image.1 hi
      exact mem_range.2 (rank_lt_card S f ha)
    · rw [card_range, card_image_of_injOn (rank_injOn S f hf)]
  obtain ⟨a, ha, h⟩ := mem_image.1 (h1 ▸ mem_range.2 hj : j ∈ S.image _)
  exact ⟨a, ha, h⟩

end Rank

/-! ### The lexicographic list of the partitions of h -/

/-- A partition is determined by its nonincreasing sequence. -/
theorem desc_injective : Function.Injective desc := fun μ ν h => by
  have h1 : ((desc μ : List ℕ) : Multiset ℕ) = desc ν := by rw [h]
  unfold desc at h1
  rw [Multiset.sort_eq, Multiset.sort_eq] at h1
  exact GeneralPieces.Ring.toN_injective h1

/-- Different partitions of h have different numbers. -/
theorem lexNum_injOn (h : ℕ) : Set.InjOn (lexNum h) (ptns h) := rank_injOn (ptns h) desc desc_injective.injOn

/-- Every j < p(h) is the number of a partition of h. -/
theorem exists_lexNum_eq {h j : ℕ} (hj : j < Partitions.p h) : ∃ μ ∈ ptns h, lexNum h μ = j :=
  exists_rank_eq (ptns h) desc desc_injective.injOn (by rwa [GeneralPieces.Ring.card_ptns])

/-! ### A string read as an integer -/

/-- A string read as an integer is the sum of the 2^i over the positions i of its ones. -/
theorem val_eq {lam : ℕ} (x : Pieces.Bits lam) : val x = ∑ i ∈ (univ.filter fun i : Fin lam => x i = true).map Fin.valEmbedding, 2 ^ i := by
  unfold AppHalfPieces.val
  rw [sum_map, sum_filter]
  rfl

/-- A string of λ bits, read as an integer, is below 2^λ. -/
theorem val_lt {lam : ℕ} (x : Pieces.Bits lam) : val x < 2 ^ lam := by
  rw [val_eq]
  refine Nat.geomSum_lt (le_refl 2) fun i hi => ?_
  obtain ⟨j, _, rfl⟩ := mem_map.1 hi
  exact j.isLt

/-- Different strings are different integers. -/
theorem val_injective (lam : ℕ) : Function.Injective (val (lam := lam)) := fun x y h => by
  rw [val_eq, val_eq] at h
  have h1 := map_injective _ (Finset.geomSum_injective (le_refl 2) h)
  funext i
  have h2 : x i = true ↔ y i = true := by
    have := Finset.ext_iff.1 h1 i
    simpa using this
  cases hx : x i <;> cases hy : y i <;> simp_all

/-! ### The function μ -/

/-- μ is injective. -/
theorem IsMu.injective {lam h : ℕ} {mu : Pieces.Bits lam → Ptn} (hmu : IsMu lam h mu) : Function.Injective mu := fun x y hxy =>
  val_injective lam (by rw [← (hmu x).2, ← (hmu y).2, hxy])

/-- μ(x) is a partition of h. -/
theorem IsMu.wt {lam h : ℕ} {mu : Pieces.Bits lam → Ptn} (hmu : IsMu lam h mu) (x : Pieces.Bits lam) : AppHalfPieces.wt (mu x) = h :=
  (GeneralPieces.Ring.mem_ptns h _).1 (hmu x).1

/-- If 2^λ ≤ p(h), there is exactly one function μ such that μ(x) is the partition of h with number
x in the lexicographic list. -/
theorem existsUnique_isMu {lam h : ℕ} (hp : 2 ^ lam ≤ Partitions.p h) : ∃! mu : Pieces.Bits lam → Ptn, IsMu lam h mu := by
  choose mu h1 h2 using fun x : Pieces.Bits lam => exists_lexNum_eq ((val_lt x).trans_le hp)
  refine ⟨mu, fun x => ⟨h1 x, h2 x⟩, fun mu' h' => funext fun x => ?_⟩
  exact lexNum_injOn h (h' x).1 (h1 x) ((h' x).2.trans (h2 x).symm)

end GeneralPieces.Lex

namespace GeneralPieces

/-- There is an h ≥ 2 with p(h) ≥ 2^λ, so "the least integer h ≥ 2 with p(h) ≥ 2^λ" is defined. -/
theorem hOfSpec : AppHalfPieces.HOfSpec := fun lam => by
  rw [Lex.hOf_eq]
  refine ⟨ClauseBound.Part.two_le_hOf lam, ClauseBound.Part.two_pow_le_p_hOf lam, fun h h1 h2 => ?_⟩
  unfold ClauseBound.Part.hOf
  exact Nat.find_min' _ ⟨h1, h2⟩

end GeneralPieces
