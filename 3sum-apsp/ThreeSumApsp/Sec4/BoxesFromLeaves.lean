/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec4.Lemma27_28

/-!
# The boxes of an output string, from its leaves of order exactly `t` (Section 4.2)

Let `η` be an output string (the paper's w) with inner set `Q` of `m` levels. The boxes of `η` are
the cubes of the sets `𝓑_V`, over all `V ⊆ Q` with `|V| = m - t`. This file proves two passages of
the running text of Section 4.2 about them.

* *Every box of `η` has exactly `m - t` symbols that are `P₀` or stars*
  (`card_starLevels_add_card_P0Levels`).
* *The second description.* Take a leaf of order exactly `t` contributing to `η` and replace its
  `P₀` by a star at every level of `Q` below the lowest level of `Q` at which it chooses another
  term, or at every level of `Q` if `t = 0` (`starBelow`). For such a leaf this is the box of the
  leaf (`boxOfLeaf_eq_starBelow`), so it is a box of `η` (`starBelow_mem`). Replacing the stars with
  `P₀` gives the leaf back (`starsToP0_starBelow`), and it turns every box of `η` into a leaf of
  order exactly `t` contributing to `η` (`starsToP0_of_mem`). So each box of `η` arises exactly once
  (`existsUnique_starBelow_eq`).
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

variable {L m t : ℕ} {η : OutStr L} {τ : Leaf L}

/-- Section 4.2: "the boxes of an output string all have exactly m - t symbols that are P₀ or
stars." -/
theorem card_starLevels_add_card_P0Levels {π : Cube L} (hπ : π ∈ (Vsets m t η).biUnion (BV η)) :
    (Cube.starLevels π).card + (Cube.P0Levels π).card = m - t := by
  obtain ⟨V, hV, hπV⟩ := mem_biUnion.1 hπ
  rw [← card_union_of_disjoint (Cube.disjoint_starLevels_P0Levels π),
    BV_starLevels_union_P0Levels hπV, (mem_powersetCard.1 hV).2]

/-- Section 4.2, for a leaf `τ` of order exactly `t` contributing to `η`: "consider the lowest level
of Q at which it chooses a term other than P₀, and replace its P₀ by a star at every lower level of
Q (or at every level of Q, if t = 0)." With `Z` the set of the levels of `Q` at which `τ` chooses
`P₀`, these lower levels are those of `F_Z`, which is all of `Q` if `Z = Q`. -/
def starBelow (η : OutStr L) (τ : Leaf L) : Cube L :=
  Cube.starAt (FV (innerSetO η) (Zof (innerSetO η) τ)) τ

/-- A leaf of order exactly `t` contributing to `η` chooses `P₀` at exactly `m - t` levels. -/
private lemma card_Zof_eq (hτ : Leaf.Contributes τ η) (hord : order m τ = t) :
    (Zof (innerSetO η) τ).card = m - t := by
  have := order_eq_sub_card_Zof m η τ hτ
  omega

/-- A set `Z` of `m - t` levels needs no padding: `V = Z`. -/
private lemma Vof_eq_self (Q Z : Finset (Fin L)) (hZ : Z.card = m - t) : Vof m t Q Z = Z := by
  simp [Vof, lowest, hZ]

/-- For a leaf of order exactly `t` contributing to `η`, the cube of the second description is the
box of the leaf. -/
theorem boxOfLeaf_eq_starBelow (hτ : Leaf.Contributes τ η) (hord : order m τ = t) :
    boxOfLeaf m t η τ = starBelow η τ := by
  rw [boxOfLeaf, starBelow, Vof_eq_self _ _ (card_Zof_eq hτ hord)]

/-- A leaf is a leaf of the cube of the second description. -/
theorem mem_leaves_starBelow (η : OutStr L) (τ : Leaf L) : τ ∈ Cube.leaves (starBelow η τ) :=
  Cube.mem_leaves_starAt _ τ

/-- Section 4.2: "The result is a box of w". -/
theorem starBelow_mem (hτ : Leaf.Contributes τ η) (hord : order m τ = t) :
    starBelow η τ ∈ (Vsets m t η).biUnion (BV η) := by
  have hmem := boxOfLeaf_mem_BV m t hτ
  rw [boxOfLeaf_eq_starBelow hτ hord, Vof_eq_self _ _ (card_Zof_eq hτ hord)] at hmem
  exact mem_biUnion.2 ⟨_, mem_powersetCard.2 ⟨filter_subset _ _, card_Zof_eq hτ hord⟩, hmem⟩

/-- The stars of `starBelow η τ` stand where `τ` chooses `P₀`, so replacing them with `P₀` gives `τ`
back. -/
theorem starsToP0_starBelow (η : OutStr L) (τ : Leaf L) : Cube.starsToP0 (starBelow η τ) = τ :=
  Cube.starsToP0_starAt fun _ hℓ => mem_P0Levels.2 (mem_filter.1 (FV_subset _ _ hℓ)).2

/-- Replacing the stars of a box of `η` with `P₀` gives a leaf of order exactly `t` contributing to
`η`. -/
theorem starsToP0_of_mem (ht : t ≤ m) (hη : (innerSetO η).card = m) {π : Cube L}
    (hπ : π ∈ (Vsets m t η).biUnion (BV η)) :
    Leaf.Contributes (Cube.starsToP0 π) η ∧ order m (Cube.starsToP0 π) = t := by
  refine ⟨((lemma_28_leaves m t ht η hη _).2 ⟨π, hπ, Cube.starsToP0_mem_leaves π⟩).1, ?_⟩
  rw [order, card_P0Levels_starsToP0, card_starLevels_add_card_P0Levels hπ]
  omega

/-- Section 4.2: "each box of w arises exactly once in this way", from the leaves of order exactly
`t` contributing to `η`. -/
theorem existsUnique_starBelow_eq (ht : t ≤ m) (hη : (innerSetO η).card = m) {π : Cube L}
    (hπ : π ∈ (Vsets m t η).biUnion (BV η)) :
    ∃! τ : Leaf L, (Leaf.Contributes τ η ∧ order m τ = t) ∧ starBelow η τ = π := by
  obtain ⟨hτ, hord⟩ := starsToP0_of_mem ht hη hπ
  refine ⟨Cube.starsToP0 π, ⟨⟨hτ, hord⟩, ?_⟩, ?_⟩
  · -- both are boxes of `η` with this leaf, and by Lemma 28 there is only one
    exact (lemma_28_unique m t ht η hη _ hτ hord.ge).unique
      ⟨starBelow_mem hτ hord, mem_leaves_starBelow η _⟩ ⟨hπ, Cube.starsToP0_mem_leaves π⟩
  · rintro τ ⟨-, rfl⟩
    exact (starsToP0_starBelow η τ).symm

end ThreeSumApsp
