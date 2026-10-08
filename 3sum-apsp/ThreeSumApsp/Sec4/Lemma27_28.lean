/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec4.Boxes

/-!
# Lemmas 27 and 28: the boxes of an output string (Section 4.2)

Let `η` be an output string (the paper's w) with inner set `Q` of `m` levels. A leaf `τ`
contributing to `η` chooses `P₀` at the set `Z` of levels of `Q`; `V` is `Z` padded from the bottom
to `m - t` levels; `F_V` is the longest initial segment of `Q` contained in `V`; and `𝓑_V` is the
set of the cubes with stars at `F_V`, with `P₀` at `V ∖ F_V`, with one of the nine terms `P_ij` at
each level of `Q ∖ V`, and with the terms of the private leaf of `η` outside `Q`. The file follows
the paper's order, except that Figure 10 comes after the definitions that it illustrates.

* *The sets `Z`, `V`, `F_V`.* The set `V` has `m - t` levels (`card_Vof`). The definition of `F_V`
  is the printed one (`FV_eq`). The condition `V ∖ F_V ⊆ Z` says that every level of `V ∖ Z` is
  below every level of `Q ∖ V` (`sdiff_FV_subset_iff`); this carries Lemma 27.
* *The sets `𝓑_V`.* They have `9^t` cubes (`card_BV`), which are boxes (`BV_isBox`), and they are
  disjoint (`BV_pairwiseDisjoint`). The box of a leaf is in `𝓑_V` for the `V` of the leaf
  (`boxOfLeaf_mem_BV`). A leaf contributing to `η` is a leaf of a box of `𝓑_V` if and only if
  `V ∖ F_V ⊆ Z ⊆ V` (`exists_mem_BV_leaf_iff`), and then of exactly one (`BV_leaf_unique`).
* *Figure 10*, for `m = 4` and `t = 2` (`figure_10_counts`, `figure_10_rows`, `figure_10_Vof`).
* **Lemma 27** (`lemma_27`): for `|Z| ≤ m - t`, the only `V` of `m - t` levels with
  `V ∖ F_V ⊆ Z ⊆ V` is `Z` padded from the bottom.
* **Lemma 28**: the leaves of order at least `t` contributing to `η` are the leaves of the boxes of
  the sets `𝓑_V` (`lemma_28_leaves`), and each of them lies in exactly one box (`lemma_28_unique`).
  So a sum over the leaves contributing to `η` splits into the leaves of order below `t` and the
  boxes (`Lemma28.sum_contributing`). For the products at the leaves this is the equation of the
  lemma (`lemma_28`), and for the constant 1 it counts the leaves (`Lemma28.card_leaves`). The
  numbers of terms are `∑_{d < t} α_d` and `α_t` (`lemma_28_counts`).
-/

@[expose] public section

open Finset

namespace ThreeSumApsp

variable {L : ℕ}

/-! ### The sets `Z`, `V` and `F_V` (Section 4.2) -/

/-- Section 4.2: "Z := {ℓ ∈ Q : τ_ℓ = P₀} (the levels at which τ chooses P₀)". -/
def Zof (Q : Finset (Fin L)) (τ : Leaf L) : Finset (Fin L) :=
  Q.filter fun ℓ => τ ℓ = Term.P0

/-- Section 2.4.3: a leaf contributes to `η` exactly if it agrees with the private leaf of `η`
outside the inner set. -/
private lemma contributes_iff_eq_privateLeaf (η : OutStr L) (τ : Leaf L) :
    Leaf.Contributes τ η ↔ ∀ ℓ, ℓ ∉ innerSetO η → τ ℓ = privateLeaf η ℓ := by
  refine forall_congr' fun ℓ => ?_
  rw [Term.contributes_iff, mem_innerSetO]
  exact or_iff_not_imp_left

/-- Outside the inner set the private leaf does not choose `P₀`. -/
private lemma privateLeaf_ne_P0 {η : OutStr L} {ℓ : Fin L} (hℓ : ℓ ∉ innerSetO η) :
    privateLeaf η ℓ ≠ Term.P0 :=
  fun h => hℓ (mem_innerSetO.2 ((OutVar.privateTerm_eq_P0_iff _).1 h))

/-- `Z` is a set of levels of `Q`. -/
private lemma Zof_subset (Q : Finset (Fin L)) (τ : Leaf L) : Zof Q τ ⊆ Q :=
  filter_subset _ _

/-- A leaf contributing to `η` chooses `P₀` exactly at the levels of `Z`. -/
private lemma P0Levels_eq_Zof (η : OutStr L) (τ : Leaf L) (hτ : Leaf.Contributes τ η) :
    P0Levels τ = Zof (innerSetO η) τ := by
  ext ℓ
  rw [Zof, mem_filter, mem_P0Levels]
  exact ⟨fun h => ⟨P0Levels_subset hτ (mem_P0Levels.2 h), h⟩, fun h => h.2⟩

/-- Section 4.2: "the order of τ is m - |Z|", for a leaf `τ` contributing to an output string `η`
with inner set `Q`. -/
theorem order_eq_sub_card_Zof (m : ℕ) (η : OutStr L) (τ : Leaf L)
    (hτ : Leaf.Contributes τ η) :
    order m τ = (m : ℤ) - ((Zof (innerSetO η) τ).card : ℤ) := by
  rw [order, P0Levels_eq_Zof η τ hτ]

/-- A leaf of order at least `t` contributing to `η` chooses `P₀` at most `m - t` times. -/
private lemma card_Zof_le {m t : ℕ} {η : OutStr L} {τ : Leaf L} (hτ : Leaf.Contributes τ η)
    (hord : (t : ℤ) ≤ order m τ) : (Zof (innerSetO η) τ).card ≤ m - t := by
  have := order_eq_sub_card_Zof m η τ hτ
  omega

/-- `V` is a set of levels of `Q`. -/
theorem Vof_subset (m t : ℕ) {Q Z : Finset (Fin L)} (hZ : Z ⊆ Q) : Vof m t Q Z ⊆ Q :=
  union_subset hZ ((lowest_subset _ _).trans sdiff_subset)

/-- Section 4.2: "the set V has exactly m - t levels". -/
theorem card_Vof {m t : ℕ} (ht : t ≤ m) {Q Z : Finset (Fin L)} (hQ : Q.card = m) (hZ : Z ⊆ Q)
    (hZc : Z.card ≤ m - t) : (Vof m t Q Z).card = m - t := by
  have hdisj : Disjoint Z (lowest (m - t - Z.card) (Q \ Z)) :=
    disjoint_of_subset_right (lowest_subset _ _) disjoint_sdiff
  rw [Vof, card_union_of_disjoint hdisj, card_lowest, card_sdiff_of_subset hZ, hQ]
  -- `|Z| + min (m - t - |Z|) (m - |Z|) = m - t`, because `|Z| ≤ m - t ≤ m`
  omega

/-- `V` is `Z` "padded from the bottom" (Section 4.2): the levels added to `Z` are below the levels
of `Q` that are left out. -/
private lemma Vof_sdiff_lt (m t : ℕ) (Q Z : Finset (Fin L)) :
    ∀ ℓ ∈ Vof m t Q Z \ Z, ∀ ℓ' ∈ Q \ Vof m t Q Z, ℓ < ℓ' := by
  intro ℓ hℓ ℓ' hℓ'
  obtain ⟨hV, hZ⟩ := mem_sdiff.1 hℓ
  obtain ⟨hQ', hV'⟩ := mem_sdiff.1 hℓ'
  obtain ⟨hZ', hlow'⟩ := not_or.1 (mt mem_union.2 hV')
  -- `ℓ` is one of the lowest levels of `Q ∖ Z`, and `ℓ'` is another level of `Q ∖ Z`
  exact lowest_lt ((mem_union.1 hV).resolve_left hZ)
    (mem_sdiff.2 ⟨mem_sdiff.2 ⟨hQ', hZ'⟩, hlow'⟩)

/-- Section 4.2: the definition `FV` agrees with the paper's two cases: "F_V := {ℓ ∈ Q : ℓ < min(Q ∖
V)}", "with F_V := Q if V = Q". -/
theorem FV_eq (Q V : Finset (Fin L)) :
    FV Q Q = Q ∧ ∀ h : (Q \ V).Nonempty, FV Q V = Q.filter fun ℓ => ℓ < (Q \ V).min' h := by
  refine ⟨by simp [FV], fun h => filter_congr fun ℓ _ => ?_⟩
  rw [lt_min'_iff]

/-- Section 4.2: `F_V` "is the longest initial segment of Q contained in V". Here: it is contained
in `V`. -/
theorem FV_subset (Q V : Finset (Fin L)) : FV Q V ⊆ V := by
  intro ℓ hℓ
  by_contra hV
  exact lt_irrefl ℓ ((mem_filter.1 hℓ).2 ℓ (mem_sdiff.2 ⟨(mem_filter.1 hℓ).1, hV⟩))

/-- Section 4.2: `F_V` "is the longest initial segment of Q contained in V". Here: it is an initial
segment of `Q`. -/
private lemma mem_FV_of_le {Q V : Finset (Fin L)} {ℓ ℓ' : Fin L} (hℓ : ℓ ∈ FV Q V)
    (hℓ' : ℓ' ∈ Q) (hle : ℓ' ≤ ℓ) : ℓ' ∈ FV Q V :=
  mem_filter.2 ⟨hℓ', fun x hx => hle.trans_lt ((mem_filter.1 hℓ).2 x hx)⟩

/-- The core of the proof of Lemma 27: "V ∖ F_V ⊆ Z says that every level of V ∖ Z is below" the
lowest level, that is every level, of `Q ∖ V`. The paper's case `V = Q` needs no separate treatment:
then `Q ∖ V` is empty. -/
private lemma sdiff_FV_subset_iff {Q V Z : Finset (Fin L)} (hV : V ⊆ Q) :
    V \ FV Q V ⊆ Z ↔ ∀ ℓ ∈ V \ Z, ∀ ℓ' ∈ Q \ V, ℓ < ℓ' := by
  constructor
  · intro h ℓ hℓ ℓ' hℓ'
    obtain ⟨hℓV, hℓZ⟩ := mem_sdiff.1 hℓ
    have hℓF : ℓ ∈ FV Q V := by
      by_contra hF
      exact hℓZ (h (mem_sdiff.2 ⟨hℓV, hF⟩))
    exact (mem_filter.1 hℓF).2 ℓ' hℓ'
  · intro h ℓ hℓ
    obtain ⟨hℓV, hℓF⟩ := mem_sdiff.1 hℓ
    by_contra hZ
    exact hℓF (mem_filter.2 ⟨hV hℓV, h ℓ (mem_sdiff.2 ⟨hℓV, hZ⟩)⟩)

/-! ### The sets `𝓑_V` (Section 4.2) -/

section BV

variable {η : OutStr L} {V : Finset (Fin L)} {π : Cube L} {ℓ : Fin L}

/-- A cube of `𝓑_V` has a star at each level of `F_V`. -/
private lemma BV_star (hπ : π ∈ BV η V) (hℓ : ℓ ∈ FV (innerSetO η) V) : π ℓ = CubeSymbol.star :=
  ((mem_filter.1 hπ).2 ℓ).1 hℓ

/-- A cube of `𝓑_V` has `P₀` at each level of `V ∖ F_V`. -/
private lemma BV_P0 (hπ : π ∈ BV η V) (hℓ : ℓ ∈ V \ FV (innerSetO η) V) :
    π ℓ = CubeSymbol.term Term.P0 :=
  ((mem_filter.1 hπ).2 ℓ).2.1 hℓ

/-- A cube of `𝓑_V` has one of the nine terms `P_ij` at each level of `Q ∖ V`. -/
private lemma BV_nine (hπ : π ∈ BV η V) (hℓ : ℓ ∈ innerSetO η \ V) :
    ∃ i j, π ℓ = CubeSymbol.term (Term.P i j) :=
  ((mem_filter.1 hπ).2 ℓ).2.2.1 hℓ

/-- A cube of `𝓑_V` has the term of the private leaf of `η` at each level outside `Q`. -/
private lemma BV_outside (hπ : π ∈ BV η V) (hℓ : ℓ ∉ innerSetO η) :
    π ℓ = CubeSymbol.term (privateLeaf η ℓ) :=
  ((mem_filter.1 hπ).2 ℓ).2.2.2 hℓ

/-- Every level is of one of the four kinds in the definition of `𝓑_V`. -/
private lemma level_cases (Q V : Finset (Fin L)) (ℓ : Fin L) :
    ℓ ∈ FV Q V ∨ ℓ ∈ V \ FV Q V ∨ ℓ ∈ Q \ V ∨ ℓ ∉ Q := by
  simp only [mem_sdiff]
  tauto

/-- The stars of a cube of `𝓑_V` are at the levels of `F_V`. -/
theorem BV_starLevels (hπ : π ∈ BV η V) : Cube.starLevels π = FV (innerSetO η) V := by
  ext ℓ
  rw [Cube.mem_starLevels]
  refine ⟨fun h => ?_, BV_star hπ⟩
  rcases level_cases (innerSetO η) V ℓ with hℓ | hℓ | hℓ | hℓ
  · exact hℓ
  · simp [BV_P0 hπ hℓ] at h
  · obtain ⟨i, j, hij⟩ := BV_nine hπ hℓ
    simp [hij] at h
  · simp [BV_outside hπ hℓ] at h

/-- The symbols `P₀` of a cube of `𝓑_V` are at the levels of `V ∖ F_V`. -/
theorem BV_P0Levels (hπ : π ∈ BV η V) : Cube.P0Levels π = V \ FV (innerSetO η) V := by
  ext ℓ
  rw [Cube.mem_P0Levels]
  refine ⟨fun h => ?_, BV_P0 hπ⟩
  rcases level_cases (innerSetO η) V ℓ with hℓ | hℓ | hℓ | hℓ
  · simp [BV_star hπ hℓ] at h
  · exact hℓ
  · obtain ⟨i, j, hij⟩ := BV_nine hπ hℓ
    simp [hij] at h
  · rw [BV_outside hπ hℓ] at h
    exact absurd (CubeSymbol.term.inj h) (privateLeaf_ne_P0 hℓ)

/-- The levels at which a cube of `𝓑_V` has a star or `P₀` are those of `V`. -/
theorem BV_starLevels_union_P0Levels (hπ : π ∈ BV η V) :
    Cube.starLevels π ∪ Cube.P0Levels π = V := by
  rw [BV_starLevels hπ, BV_P0Levels hπ, union_sdiff_of_subset (FV_subset _ _)]

/-- Two cubes of `𝓑_V` with the same symbols at the levels of `Q ∖ V` are equal. -/
private lemma BV_ext {π' : Cube L} (hπ : π ∈ BV η V) (hπ' : π' ∈ BV η V)
    (h : ∀ ℓ ∈ innerSetO η \ V, π ℓ = π' ℓ) : π = π' := by
  funext ℓ
  rcases level_cases (innerSetO η) V ℓ with hℓ | hℓ | hℓ | hℓ
  · rw [BV_star hπ hℓ, BV_star hπ' hℓ]
  · rw [BV_P0 hπ hℓ, BV_P0 hπ' hℓ]
  · exact h ℓ hℓ
  · rw [BV_outside hπ hℓ, BV_outside hπ' hℓ]

/-- At a level of `Q ∖ V`, a cube of `𝓑_V` has the term of each of its leaves. -/
private lemma BV_eq_term_of_leaf (hπ : π ∈ BV η V) {τ : Leaf L} (hτ : τ ∈ Cube.leaves π)
    (hℓ : ℓ ∈ innerSetO η \ V) : π ℓ = CubeSymbol.term (τ ℓ) := by
  obtain ⟨i, j, hij⟩ := BV_nine hπ hℓ
  rw [hij, Cube.eq_of_mem_leaves hτ hij]

end BV

/-- The symbols allowed at level `ℓ` in a cube of `𝓑_V`. -/
private def allowed (η : OutStr L) (V : Finset (Fin L)) (ℓ : Fin L) : Finset CubeSymbol :=
  univ.filter fun s =>
    (ℓ ∈ FV (innerSetO η) V → s = CubeSymbol.star) ∧
    (ℓ ∈ V \ FV (innerSetO η) V → s = CubeSymbol.term Term.P0) ∧
    (ℓ ∈ innerSetO η \ V → ∃ i j, s = CubeSymbol.term (Term.P i j)) ∧
    (ℓ ∉ innerSetO η → s = CubeSymbol.term (privateLeaf η ℓ))

/-- `𝓑_V` is the set of all cubes with an allowed symbol at every level. -/
private lemma BV_eq_piFinset (η : OutStr L) (V : Finset (Fin L)) :
    BV η V = Fintype.piFinset (allowed η V) := by
  ext π
  simp [BV, allowed, Fintype.mem_piFinset]

/-- Nine symbols are allowed at a level of `Q ∖ V`, and one at every other level. -/
private lemma card_allowed (η : OutStr L) (V : Finset (Fin L)) (hV : V ⊆ innerSetO η)
    (ℓ : Fin L) : (allowed η V ℓ).card = if ℓ ∈ innerSetO η \ V then 9 else 1 := by
  have hnine :
      (univ.filter fun s : CubeSymbol => ∃ i j, s = CubeSymbol.term (Term.P i j)).card = 9 := by
    decide
  have hFV := @FV_subset L (innerSetO η) V ℓ
  have hVQ := @hV ℓ
  unfold allowed
  by_cases hF : ℓ ∈ FV (innerSetO η) V
  · simp [hF, hFV hF, hVQ (hFV hF), filter_eq']
  by_cases hℓV : ℓ ∈ V
  · simp [hF, hℓV, hVQ hℓV, filter_eq']
  by_cases hℓQ : ℓ ∈ innerSetO η
  · simp [hF, hℓV, hℓQ, hnine]
  · simp [hF, hℓV, hℓQ, filter_eq']

/-- Section 4.2: `𝓑_V` is "the set of the 9^t cubes π with" the symbols above. -/
theorem card_BV (m t : ℕ) (ht : t ≤ m) (η : OutStr L) (hη : (innerSetO η).card = m)
    (V : Finset (Fin L)) (hV : V ∈ Vsets m t η) : (BV η V).card = 9 ^ t := by
  obtain ⟨hVQ, hVc⟩ := mem_powersetCard.1 hV
  rw [BV_eq_piFinset η V, Fintype.card_piFinset]
  simp only [card_allowed η V hVQ]
  rw [prod_ite_mem_const, one_pow, mul_one, card_sdiff_of_subset hVQ, hη, hVc,
    Nat.sub_sub_self ht]

/-- Section 4.2: "Every cube in 𝓑_V is a box: it satisfies condition (i) of the definition because
it has |V| = m - t symbols P₀ or stars, and condition (ii) because its stars are below its symbols
P₀, since F_V is an initial segment of Q." -/
theorem BV_isBox {m t : ℕ} {η : OutStr L} {V : Finset (Fin L)} (hV : V ∈ Vsets m t η) {π : Cube L}
    (hπ : π ∈ BV η V) : IsBox m t π := by
  obtain ⟨hVQ, hVc⟩ := mem_powersetCard.1 hV
  rw [IsBox, BV_starLevels hπ, BV_P0Levels hπ, add_comm,
    card_sdiff_add_card_eq_card (FV_subset _ _)]
  refine ⟨hVc.le, fun ℓ hℓ ℓ' hℓ' => ?_⟩
  -- otherwise `ℓ' ≤ ℓ` would be a level of the initial segment `F_V`
  obtain ⟨hℓ'V, hℓ'F⟩ := mem_sdiff.1 hℓ'
  by_contra hlt
  exact hℓ'F (mem_FV_of_le hℓ (hVQ hℓ'V) (not_lt.1 hlt))

/-- The sets `𝓑_V` for different `V` are disjoint, so that the double sum `∑_V ∑_{π ∈ 𝓑_V}` of Lemma
28 runs over each box of `⋃_V 𝓑_V` once. -/
theorem BV_pairwiseDisjoint (η : OutStr L) (s : Set (Finset (Fin L))) :
    s.PairwiseDisjoint (BV η) :=
  -- a cube of `𝓑_V` determines `V`
  fun _ _ _ _ hne => disjoint_left.2 fun _ hπ hπ' =>
    hne ((BV_starLevels_union_P0Levels hπ).symm.trans (BV_starLevels_union_P0Levels hπ'))

/-- If `τ` contributes to `η` and `V ∖ F_V ⊆ Z ⊆ V`, then `τ` with stars at the levels of `F_V` is a
cube of `𝓑_V`. -/
private lemma starAt_mem_BV {η : OutStr L} {V : Finset (Fin L)} {τ : Leaf L}
    (hτ : Leaf.Contributes τ η) (hVZ : V \ FV (innerSetO η) V ⊆ Zof (innerSetO η) τ)
    (hZV : Zof (innerSetO η) τ ⊆ V) : Cube.starAt (FV (innerSetO η) V) τ ∈ BV η V := by
  refine mem_filter.2
    ⟨mem_univ _, fun ℓ => ⟨fun hF => if_pos hF, fun hVF => ?_, fun hQV => ?_, fun hQ => ?_⟩⟩
  · -- at a level of `V ∖ F_V`, which is a level of `Z`, the leaf chooses `P₀`
    rw [Cube.starAt, if_neg (mem_sdiff.1 hVF).2, (mem_filter.1 (hVZ hVF)).2]
  · -- at a level of `Q ∖ V`, which is not a level of `Z`, the leaf chooses another term
    obtain ⟨hQ, hV⟩ := mem_sdiff.1 hQV
    rw [Cube.starAt, if_neg fun hF => hV (FV_subset _ _ hF)]
    cases hterm : τ ℓ with
    | P i j => exact ⟨i, j, rfl⟩
    | P0 => exact absurd (hZV (mem_filter.2 ⟨hQ, hterm⟩)) hV
  · -- outside `Q` the leaf agrees with the private leaf
    rw [Cube.starAt, if_neg fun hF : ℓ ∈ FV (innerSetO η) V => hQ (mem_filter.1 hF).1,
      (contributes_iff_eq_privateLeaf η τ).1 hτ ℓ hQ]

/-- Section 4.2: the box of a leaf `τ` of order at least `t` contributing to `η`: "The box of τ then
agrees with τ everywhere, except that it has a star at every level of Q below the level where we
stopped", these levels being those of `F_V` for the `V` of `τ`. -/
def boxOfLeaf (m t : ℕ) (η : OutStr L) (τ : Leaf L) : Cube L :=
  Cube.starAt (FV (innerSetO η) (Vof m t (innerSetO η) (Zof (innerSetO η) τ))) τ

/-- A leaf is a leaf of its box. -/
theorem mem_leaves_boxOfLeaf (m t : ℕ) (η : OutStr L) (τ : Leaf L) :
    τ ∈ Cube.leaves (boxOfLeaf m t η τ) :=
  Cube.mem_leaves_starAt _ τ

/-- Section 4.2: "When V is the set defined above from a leaf τ, the box of τ is the one in 𝓑_V with
the terms of τ at the levels of Q ∖ V": it is a cube of `𝓑_V`, for the set `V` of `τ`. -/
theorem boxOfLeaf_mem_BV (m t : ℕ) {η : OutStr L} {τ : Leaf L} (hτ : Leaf.Contributes τ η) :
    boxOfLeaf m t η τ ∈ BV η (Vof m t (innerSetO η) (Zof (innerSetO η) τ)) :=
  starAt_mem_BV hτ
    ((sdiff_FV_subset_iff (Vof_subset m t (Zof_subset _ τ))).2 (Vof_sdiff_lt m t _ _))
    subset_union_left

/-- Section 4.2: "A leaf contributing to w that chooses P₀ at the set Z of levels is a leaf of a box
of 𝓑_V if and only if it chooses P₀ at every level of V ∖ F_V and at no level of Q ∖ V, that is, V ∖
F_V ⊆ Z ⊆ V". -/
theorem exists_mem_BV_leaf_iff {η : OutStr L} {V : Finset (Fin L)} (hV : V ⊆ innerSetO η)
    {τ : Leaf L} (hτ : Leaf.Contributes τ η) :
    (∃ π ∈ BV η V, τ ∈ Cube.leaves π) ↔
      V \ FV (innerSetO η) V ⊆ Zof (innerSetO η) τ ∧ Zof (innerSetO η) τ ⊆ V := by
  constructor
  · rintro ⟨π, hπ, hτπ⟩
    refine ⟨fun ℓ hℓ => mem_filter.2 ⟨hV (mem_sdiff.1 hℓ).1, ?_⟩, fun ℓ hℓ => ?_⟩
    · exact Cube.eq_of_mem_leaves hτπ (BV_P0 hπ hℓ)
    · by_contra hℓV
      obtain ⟨hℓQ, hterm⟩ := mem_filter.1 hℓ
      obtain ⟨i, j, hij⟩ := BV_nine hπ (mem_sdiff.2 ⟨hℓQ, hℓV⟩)
      simp [Cube.eq_of_mem_leaves hτπ hij] at hterm
  · exact fun ⟨hVZ, hZV⟩ => ⟨_, starAt_mem_BV hτ hVZ hZV, Cube.mem_leaves_starAt _ τ⟩

/-- Section 4.2: "Furthermore, it is a leaf of exactly one of these boxes, namely, the one with its
terms at the levels of Q ∖ V." -/
theorem BV_leaf_unique {η : OutStr L} {V : Finset (Fin L)} {τ : Leaf L} {π π' : Cube L}
    (hπ : π ∈ BV η V) (hτπ : τ ∈ Cube.leaves π) (hπ' : π' ∈ BV η V) (hτπ' : τ ∈ Cube.leaves π') :
    π = π' :=
  BV_ext hπ hπ' fun _ hℓ =>
    (BV_eq_term_of_leaf hπ hτπ hℓ).trans (BV_eq_term_of_leaf hπ' hτπ' hℓ).symm

/-! ### Figure 10 -/

/-- Figure 10, for `m = 4` and `t = 2`: "these 6 · 81 = 486 = α₂ boxes contain each of the
α₂ + α₃ + α₄ = 9963 leaves of order at least 2". -/
theorem figure_10_counts :
    6 * 81 = 486 ∧ alpha 4 2 = 486 ∧ alpha 4 2 + alpha 4 3 + alpha 4 4 = 9963 := by
  refine ⟨by norm_num, ?_, ?_⟩ <;> simp [alpha, Nat.choose]

/-- Figure 10, the six rows, with the four levels `ℓ₁ < ℓ₂ < ℓ₃ < ℓ₄` of `Q` taken as
`0, 1, 2, 3`: the levels of `F_V`, which carry the stars; and the column "leaves per box" adds up,
over the 81 boxes of each row, to `81 · (10² + 10 + 10 + 1 + 1 + 1) = 9963`. (Here 81 and the powers
of ten are numerals.) -/
theorem figure_10_rows :
    FV (univ : Finset (Fin 4)) {0, 1} = {0, 1} ∧
      FV (univ : Finset (Fin 4)) {0, 2} = {0} ∧
      FV (univ : Finset (Fin 4)) {0, 3} = {0} ∧
      FV (univ : Finset (Fin 4)) {1, 2} = ∅ ∧
      FV (univ : Finset (Fin 4)) {1, 3} = ∅ ∧
      FV (univ : Finset (Fin 4)) {2, 3} = ∅ ∧
      81 * (10 ^ 2 + 10 + 10 + 1 + 1 + 1) = 9963 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by norm_num⟩ <;> decide

/-- Figure 10, column "sets Z of its leaves": the row `V` in which each set `Z` of at most
one level appears. (A set `Z` of two levels appears in the row `V = Z`; these six cases are not
written out.) -/
theorem figure_10_Vof :
    Vof 4 2 (univ : Finset (Fin 4)) ∅ = {0, 1} ∧
      Vof 4 2 (univ : Finset (Fin 4)) {0} = {0, 1} ∧
      Vof 4 2 (univ : Finset (Fin 4)) {1} = {0, 1} ∧
      Vof 4 2 (univ : Finset (Fin 4)) {2} = {0, 2} ∧
      Vof 4 2 (univ : Finset (Fin 4)) {3} = {0, 3} := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ### Lemma 27 -/

/-- **Lemma 27**. "Let Q be a set of m levels, and let 0 ≤ t ≤ m. For every Z ⊆ Q
with |Z| ≤ m - t, there is exactly one set V ⊆ Q with |V| = m - t and V ∖ F_V ⊆ Z ⊆ V, namely Z
together with the m - t - |Z| lowest levels of Q ∖ Z." This set is `Vof m t Q Z`. -/
theorem lemma_27 {L : ℕ} (m t : ℕ) (ht : t ≤ m) (Q Z : Finset (Fin L)) (hQ : Q.card = m)
    (hZ : Z ⊆ Q) (hZc : Z.card ≤ m - t) (V : Finset (Fin L)) :
    (V ⊆ Q ∧ V.card = m - t ∧ V \ FV Q V ⊆ Z ∧ Z ⊆ V) ↔ V = Vof m t Q Z := by
  constructor
  · rintro ⟨hVQ, hVc, hVZ, hZV⟩
    -- "Q ∖ Z is the disjoint union of V ∖ Z and Q ∖ V", and `V ∖ Z` lies below `Q ∖ V`,
    -- so "V ∖ Z consists of the lowest levels of Q ∖ Z".
    have hrest : (Q \ Z) \ (V \ Z) = Q \ V := sdiff_sdiff_sdiff_cancel_right hZV
    have hlow := eq_lowest_of_lt (sdiff_subset_sdiff hVQ (le_refl Z))
      (hrest ▸ (sdiff_FV_subset_iff hVQ).1 hVZ)
    rw [card_sdiff_of_subset hZV, hVc] at hlow
    rw [Vof, ← hlow, union_sdiff_of_subset hZV]
  · rintro rfl
    have hVQ := Vof_subset m t hZ
    exact ⟨hVQ, card_Vof ht hQ hZ hZc, (sdiff_FV_subset_iff hVQ).2 (Vof_sdiff_lt m t Q Z),
      subset_union_left⟩

/-! ### Lemma 28 -/

/-- **Lemma 28**, first sentence, first half. "Let w be an output string, with inner set
Q. The leaves of order at least t contributing to w are exactly the leaves of the boxes in ⋃_V 𝓑_V,
the union over all V ⊆ Q with |V| = m - t". -/
theorem lemma_28_leaves {L : ℕ} (m t : ℕ) (ht : t ≤ m) (η : OutStr L) (hη : (innerSetO η).card = m)
    (τ : Leaf L) :
    (Leaf.Contributes τ η ∧ (t : ℤ) ≤ order m τ) ↔
      ∃ π ∈ (Vsets m t η).biUnion (BV η), τ ∈ Cube.leaves π := by
  constructor
  · -- "Conversely, a leaf τ contributing to w, of order at least t," is a leaf of its box.
    rintro ⟨hτ, hord⟩
    refine ⟨boxOfLeaf m t η τ, mem_biUnion.2 ⟨_, mem_powersetCard.2 ?_, boxOfLeaf_mem_BV m t hτ⟩,
      mem_leaves_boxOfLeaf m t η τ⟩
    exact ⟨Vof_subset m t (Zof_subset _ τ),
      card_Vof ht hη (Zof_subset _ τ) (card_Zof_le hτ hord)⟩
  · -- "Every leaf of a box of 𝓑_V agrees with the private leaf of w outside Q, so it contributes
    -- to w", and a box only contains leaves of order at least `t`.
    rintro ⟨π, hπ, hτπ⟩
    obtain ⟨V, hV, hπV⟩ := mem_biUnion.1 hπ
    exact ⟨(contributes_iff_eq_privateLeaf η τ).2 fun ℓ hℓ =>
        Cube.eq_of_mem_leaves hτπ (BV_outside hπV hℓ),
      le_order_of_mem_leaves ht (BV_isBox hV hπV) hτπ⟩

/-- Proof of Lemma 28: "By Lemma 27, exactly one V satisfies this condition": if a leaf of order at
least `t` contributing to `η` is a leaf of a box of `𝓑_V`, then `V` is the set of the leaf. -/
private lemma eq_Vof_of_mem_leaves {m t : ℕ} (ht : t ≤ m) {η : OutStr L}
    (hη : (innerSetO η).card = m) {τ : Leaf L} (hτ : Leaf.Contributes τ η)
    (hord : (t : ℤ) ≤ order m τ) {V : Finset (Fin L)} (hV : V ∈ Vsets m t η) {π : Cube L}
    (hπ : π ∈ BV η V) (hτπ : τ ∈ Cube.leaves π) :
    V = Vof m t (innerSetO η) (Zof (innerSetO η) τ) := by
  obtain ⟨hVQ, hVc⟩ := mem_powersetCard.1 hV
  obtain ⟨hVZ, hZV⟩ := (exists_mem_BV_leaf_iff hVQ hτ).1 ⟨π, hπ, hτπ⟩
  exact (lemma_27 m t ht _ _ hη (Zof_subset _ τ) (card_Zof_le hτ hord) V).1 ⟨hVQ, hVc, hVZ, hZV⟩

/-- **Lemma 28**, first sentence, second half: "and each of them is a leaf of exactly one
of these boxes." -/
theorem lemma_28_unique {L : ℕ} (m t : ℕ) (ht : t ≤ m) (η : OutStr L) (hη : (innerSetO η).card = m)
    (τ : Leaf L) (hτ : Leaf.Contributes τ η) (hord : (t : ℤ) ≤ order m τ) :
    ∃! π : Cube L, π ∈ (Vsets m t η).biUnion (BV η) ∧ τ ∈ Cube.leaves π := by
  obtain ⟨π, hπ, hτπ⟩ := (lemma_28_leaves m t ht η hη τ).1 ⟨hτ, hord⟩
  refine ⟨π, ⟨hπ, hτπ⟩, ?_⟩
  rintro π' ⟨hπ', hτπ'⟩
  -- the two boxes belong to the same `V`, and `𝓑_V` has only one box with the leaf `τ`
  obtain ⟨V, hV, hπV⟩ := mem_biUnion.1 hπ
  obtain ⟨V', hV', hπV'⟩ := mem_biUnion.1 hπ'
  obtain rfl : V' = V := (eq_Vof_of_mem_leaves ht hη hτ hord hV' hπV' hτπ').trans
    (eq_Vof_of_mem_leaves ht hη hτ hord hV hπV hτπ).symm
  exact BV_leaf_unique hπV' hτπ' hπV hτπ

/-- The equation of Lemma 28 for an arbitrary function `g` of the leaves in the place of the
products: the sum of `g` over the leaves contributing to `η` is the sum over the leaves of order
below `t` plus the sum over the leaves of the boxes. -/
theorem Lemma28.sum_contributing {G : Type*} [AddCommMonoid G] (m t : ℕ) (ht : t ≤ m)
    (η : OutStr L) (hη : (innerSetO η).card = m) (g : Leaf L → G) :
    ∑ τ : Leaf L with Leaf.Contributes τ η, g τ =
      ∑ τ ∈ lowLeaves m t η, g τ + ∑ V ∈ Vsets m t η, ∑ π ∈ BV η V, ∑ τ ∈ Cube.leaves π, g τ := by
  have hdisjoint :
      (((Vsets m t η).biUnion (BV η) : Finset (Cube L)) : Set (Cube L)).PairwiseDisjoint
        Cube.leaves := by
    intro π hπ π' hπ' hne
    rw [Function.onFun, disjoint_left]
    intro τ hτ hτ'
    obtain ⟨hc, hord⟩ := (lemma_28_leaves m t ht η hη τ).2 ⟨π, hπ, hτ⟩
    exact hne ((lemma_28_unique m t ht η hη τ hc hord).unique ⟨hπ, hτ⟩ ⟨hπ', hτ'⟩)
  have hhigh : ((Vsets m t η).biUnion (BV η)).biUnion Cube.leaves =
      univ.filter fun τ : Leaf L => Leaf.Contributes τ η ∧ ¬ order m τ < (t : ℤ) := by
    ext τ
    rw [mem_biUnion, mem_filter, not_lt, ← lemma_28_leaves m t ht η hη τ]
    simp
  -- The sums over the sets `V`, the boxes and their leaves are one sum over the contributing leaves
  -- of order at least `t`; the contributing leaves split into those of order below `t` and these.
  rw [← sum_biUnion (BV_pairwiseDisjoint η _), ← sum_biUnion hdisjoint, hhigh, lowLeaves,
    ← filter_filter, ← filter_filter, sum_filter_add_sum_filter_not]

/-- **Lemma 28**, the displayed equation, for arbitrary input arrays: the sum of the products at the
leaves contributing to `η`, which is `Mult(a, b)[η]`, equals the sum over the leaves of order below
`t` plus the sum of the values of the boxes. See `lemma_28` for the form with `(X_Q Y_Q)[η]` on the
left. -/
theorem Lemma28.Mult_eq_querySum (m t : ℕ) (ht : t ≤ m) (a : LeftStr L → ℤ) (b : RightStr L → ℤ)
    (η : OutStr L) (hη : (innerSetO η).card = m) : Mult a b η = querySum m t a b η :=
  Lemma28.sum_contributing m t ht η hη fun τ => Phi τ a * Psi τ b

/-- **Lemma 28**, the displayed equation. "Hence (X_Q Y_Q)[w] = ∑_{τ contributing to w, of
order < t} Φ_τ(a) Ψ_τ(b) + ∑_{V ⊆ Q, |V| = m - t} ∑_{π ∈ 𝓑_V} val(π)", for the input arrays `a`, `b`
built from the matrices `X_Q`, `Y_Q` as in Section 2.3.3. The right-hand side is `querySum`. -/
theorem lemma_28 {L : ℕ} (m t : ℕ) (ht : t ≤ m) (X : Finset (Fin L) → LeftMat L m)
    (Y : Finset (Fin L) → RightMat L m) (η : OutStr L) (hη : (innerSetO η).card = m) :
    (X (innerSetO η) * Y (innerSetO η)) (rowO η hη) (colO η hη) =
      querySum m t (arrayL m X) (arrayR m Y) η := by
  rw [← lemma_9 X Y η hη, Lemma28.Mult_eq_querySum m t ht _ _ η hη]

/-- The terms of the sum of Lemma 28 stand for the `10^m` leaves contributing to `η`, each of them
once: one leaf for each product, and its leaves for each box. The bound on the partial sums of a
query (word size, the proof of Theorem 30) rests on this count. -/
theorem Lemma28.card_leaves (m t : ℕ) (ht : t ≤ m) (η : OutStr L)
    (hη : (innerSetO η).card = m) :
    (lowLeaves m t η).card + ∑ π ∈ (Vsets m t η).biUnion (BV η), (Cube.leaves π).card = 10 ^ m := by
  have hsplit := Lemma28.sum_contributing m t ht η hη fun _ => 1
  rw [← card_eq_sum_ones, card_filter_contributes η hη] at hsplit
  rw [hsplit, sum_biUnion (BV_pairwiseDisjoint η _)]
  simp

/-- The leaves of order below `t` contributing to `η`, sorted by their order, which is at least 0.
-/
private lemma lowLeaves_eq_biUnion (m t : ℕ) (η : OutStr L) (hη : (innerSetO η).card = m) :
    lowLeaves m t η = (range t).biUnion fun d =>
      univ.filter fun τ : Leaf L => Leaf.Contributes τ η ∧ order m τ = d := by
  ext τ
  simp only [lowLeaves, mem_filter, mem_univ, true_and, mem_biUnion, mem_range]
  constructor
  · rintro ⟨hτ, hlt⟩
    have hnonneg := order_nonneg hη hτ
    exact ⟨(order m τ).toNat, by omega, hτ, (Int.toNat_of_nonneg hnonneg).symm⟩
  · rintro ⟨d, hd, hτ, heq⟩
    exact ⟨hτ, by omega⟩

/-- **Lemma 28**, last line: "a sum of ∑_{d=0}^{t-1} α_d products and α_t values of
boxes."  The third clause says that these α_t cubes are different, that is, that the sets 𝓑_V are
disjoint; Section 4.2 has it in the words "w has exactly α_t boxes". -/
theorem lemma_28_counts {L : ℕ} (m t : ℕ) (ht : t ≤ m) (η : OutStr L)
    (hη : (innerSetO η).card = m) :
    (lowLeaves m t η).card = ∑ d ∈ range t, alpha m d ∧
      ∑ V ∈ Vsets m t η, (BV η V).card = alpha m t ∧
      ((Vsets m t η).biUnion (BV η)).card = alpha m t := by
  -- "there are binom(m, m-t) sets V with 9^t boxes each"
  have hsum : ∑ V ∈ Vsets m t η, (BV η V).card = alpha m t := by
    rw [sum_congr rfl fun V hV => card_BV m t ht η hη V hV, sum_const, Vsets,
      card_powersetCard, hη, Nat.choose_symm ht, smul_eq_mul, alpha]
  refine ⟨?_, hsum, ?_⟩
  · -- "α_d leaves of order d contribute to w"
    rw [lowLeaves_eq_biUnion m t η hη, card_biUnion]
    · exact sum_congr rfl fun d _ => sec2_card_contributing_of_order η hη d
    · intro d _ d' _ hne
      rw [Function.onFun, disjoint_left]
      intro τ hd hd'
      exact hne (by exact_mod_cast (mem_filter.1 hd).2.2.symm.trans (mem_filter.1 hd').2.2)
  · rw [card_biUnion (BV_pairwiseDisjoint η _), hsum]

/-- Section 4.2, on the cubes of 𝓑_V, which Lemma 28 calls "the boxes in ⋃_V 𝓑_V": "Every cube in
𝓑_V is a box: it satisfies condition (i) of the definition because it has |V| = m - t symbols P₀ or
stars, and condition (ii) because its stars are below its symbols P₀, since F_V is an initial
segment of Q."  Moreover "a box of 𝓑_V has stars at the levels of F_V", so it is one of the boxes
with |F_V| stars (`boxesWithStars`). -/
theorem lemma_28_boxes {L : ℕ} (m t : ℕ) (η : OutStr L) (V : Finset (Fin L)) (hV : V ∈ Vsets m t η)
    (π : Cube L) (hπ : π ∈ BV η V) : π ∈ boxesWithStars L m t (FV (innerSetO η) V).card :=
  mem_filter.2 ⟨mem_filter.2 ⟨mem_univ _, BV_isBox hV hπ⟩, by rw [BV_starLevels hπ]⟩

end ThreeSumApsp
