/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import UniformInK.Spars.Defs
import all SparsifyWidthK.Step
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.SplitIfs

/-! # The sparsification with geometric thresholds: one step keeps the invariant

The definitions are in proof/sparsification/UniformInK/Spars/Defs.lean. This file proves two of its
interface statements, StNodeRootU and StNodeStepU. It parallels the first part of
proof/sparsification/SparsifyWidthK/Step.lean, whose lemmas on the sets nextN N A and on the counts
nextA a r c are used as they are.

* inv_step: a step that adds a family A of sets, all of one size r, keeps the invariant InvU. At
  size r the bound on the clauses over a set Y follows from AddU.deg; at every other size N only
  loses clauses. In the inequality InvU.acc the sizes below r do not change, size r gains A and
  loses nothing, and a size i above r loses at most |A| · 2·θ(i−r) clauses, because each lost clause
  contains a set of A; the right-hand side gains exactly that much through the count at size r.
* add_light, add_heavy: both children of the rule of Impagliazzo, Paturi and Zane are such steps. A
  heart for size j is a nonempty set H with |H| < j that lies in at least θ(j−|H|) clauses of size
  j; no size below j has a heart, and no set larger than H is a heart for j.
* node_light, node_heavy: the counters of steps and of heavy steps along a path. -/

public section

namespace UniformInK

open Finset Groundwork Groundwork.Sparsify WidthK

namespace Step

variable {α : Type*} [DecidableEq α]

section StepLemma

variable {θ : ℕ → ℕ} {F A N : Finset (Finset α)} {r : ℕ} {a : ℕ → ℕ}

/-- A step in the sense of this folder is a step in the sense of
proof/sparsification/SparsifyWidthK/Defs.lean: take one-element sets Y. -/
theorem toAddK (hA : AddU θ F A r) : AddK (fun i => 2 * θ (i - 1)) F A r where
  ssub := hA.ssub
  size := hA.size
  pos := hA.pos
  deg := by
    intro y
    have := hA.deg {y} (singleton_nonempty y) (by rw [card_singleton]; exact hA.pos)
    simpa only [singleton_subset_iff, card_singleton] using this

/-- The weighted counts below size i do not change if i ≤ r. -/
theorem wsum_nextA_of_le (w a : ℕ → ℕ) (c : ℕ) {i r : ℕ} (hi : i ≤ r) :
    ∑ i' ∈ range i, w i' * nextA a r c i' = ∑ i' ∈ range i, w i' * a i' := by
  refine sum_congr rfl fun i' hi' => ?_
  have := mem_range.1 hi'
  simp only [nextA, if_neg (show i' ≠ r by omega), Nat.add_zero]

/-- The weighted counts below size i grow by w r · c if r < i. -/
theorem wsum_nextA_of_lt (w a : ℕ → ℕ) (c : ℕ) {i r : ℕ} (hi : r < i) :
    ∑ i' ∈ range i, w i' * nextA a r c i' = ∑ i' ∈ range i, w i' * a i' + w r * c := by
  simp only [nextA, Nat.mul_add, sum_add_distrib, mul_ite, Nat.mul_zero, sum_ite_eq', mem_range, if_pos hi]

/-- A step removes at most |A| · 2·θ(i−r) clauses of a size i ≥ r from N. -/
theorem card_lay_le (h : InvU θ F N a) (hA : AddU θ F A r) {i : ℕ} (hi : r ≤ i) :
    (lay N i).card ≤ ((lay N i).filter fun C => ∀ D ∈ A, ¬ D ⊆ C).card + A.card * (2 * θ (i - r)) := by
  have hsplit := card_filter_add_card_filter_not (s := lay N i) (fun C => ∀ D ∈ A, ¬ D ⊆ C)
  have hle : ((lay N i).filter fun C => ¬ ∀ D ∈ A, ¬ D ⊆ C).card ≤ A.card * (2 * θ (i - r)) := by
    refine le_trans (card_le_card ?_) (card_biUnion_le_card_mul A (fun D => (lay N i).filter fun C => D ⊆ C) (2 * θ (i - r)) ?_)
    · intro C hC
      obtain ⟨hCN, hex⟩ := mem_filter.1 hC
      simp only [not_forall, not_not] at hex
      obtain ⟨D, hD, hDC⟩ := hex
      exact mem_biUnion.2 ⟨D, hD, mem_filter.2 ⟨hCN, hDC⟩⟩
    · intro D hD
      have hne : D.Nonempty := by rw [← card_pos, hA.size D hD]; exact hA.pos
      have := h.deg i D hne (by rw [hA.size D hD]; exact hi)
      rwa [hA.size D hD] at this
  omega

/-- A step that adds A, all of size r, keeps the invariant: N becomes nextN N A, and the count at
size r grows by |A|. -/
theorem inv_step (h : InvU θ F N a) (hA : AddU θ F A r) :
    InvU θ (Sparsify.red (F ∪ A)) (nextN N A) (nextA a r A.card) where
  red := reduced_red _
  sub := by
    rw [WidthK.Step.red_union h.red (toAddK hA)]
    exact union_subset_union_right (filter_subset_filter _ h.sub)
  deg := by
    intro i Y hY hYi
    by_cases hi : i = r
    · subst hi
      rw [WidthK.Step.lay_nextN_self h.red h.sub (toAddK hA), filter_union]
      have h1 : ((lay N i).filter fun C => Y ⊆ C).card ≤ (Sparsify.over F i Y).card := by
        apply card_le_card
        intro C hC
        obtain ⟨hCN, hYC⟩ := mem_filter.1 hC
        obtain ⟨hCN, hc⟩ := mem_filter.1 hCN
        exact mem_filter.2 ⟨h.sub hCN, hc, hYC⟩
      have := card_union_le (A.filter fun C => Y ⊆ C) ((lay N i).filter fun C => Y ⊆ C)
      have := hA.deg Y hY hYi
      omega
    · rw [WidthK.Step.lay_nextN_of_ne (toAddK hA) hi]
      exact (card_le_card (filter_subset_filter _ (filter_subset _ _))).trans (h.deg i Y hY hYi)
  acc := by
    intro i
    rcases lt_trichotomy i r with hi | hi | hi
    · rw [WidthK.Step.lay_nextN_of_lt (toAddK hA) hi, wsum_nextA_of_le _ a _ hi.le]
      simpa only [nextA, if_neg hi.ne, Nat.add_zero] using h.acc i
    · subst hi
      rw [WidthK.Step.lay_nextN_self h.red h.sub (toAddK hA), wsum_nextA_of_le _ a _ le_rfl, card_union_of_disjoint]
      · have := h.acc i
        simp only [nextA, if_true]
        omega
      · rw [disjoint_left]
        intro C hCA hCN
        exact WidthK.Step.notMem h.red (toAddK hA) hCA (h.sub (mem_filter.1 hCN).1)
    · rw [WidthK.Step.lay_nextN_of_ne (toAddK hA) hi.ne', wsum_nextA_of_lt _ a _ hi]
      have h1 := h.acc i
      have h2 := card_lay_le h hA hi.le
      simp only [nextA, if_neg hi.ne', Nat.add_zero]
      rw [Nat.mul_comm A.card] at h2
      omega

end StepLemma

variable {θ : ℕ → ℕ} {k j : ℕ} {F : Finset (Finset α)} {H : Finset α}

/-- A set of r elements lies in at most one set of r elements. -/
theorem card_filter_subset_le_one {G : Finset (Finset α)} {r : ℕ} (hG : ∀ C ∈ G, C.card = r) {Y : Finset α} (hY : Y.card = r) :
    (G.filter fun C => Y ⊆ C).card ≤ 1 := by
  rw [card_le_one]
  intro C hC D hD
  obtain ⟨hC, hYC⟩ := mem_filter.1 hC
  obtain ⟨hD, hYD⟩ := mem_filter.1 hD
  rw [← eq_of_subset_of_card_le hYC (by rw [hG C hC, hY]), ← eq_of_subset_of_card_le hYD (by rw [hG D hD, hY])]

/-- Below the size j of the rule every nonempty set Y of at most r literals lies in at most θ(r−|Y|)
clauses of size r. -/
theorem card_over_le (hθ : ∀ i, 1 ≤ θ i) (hB : Rule θ k F j H) {r : ℕ} (hr : r < j) {Y : Finset α} (hY : Y.Nonempty) (hYr : Y.card ≤ r) :
    (Sparsify.over F r Y).card ≤ θ (r - Y.card) := by
  rcases hYr.eq_or_lt with he | hlt
  · refine le_trans ?_ (hθ _)
    have := card_filter_subset_le_one (G := F.filter fun C => C.card = r) (fun C hC => (mem_filter.1 hC).2) he
    simpa only [Sparsify.over, filter_filter] using this
  · by_contra hc
    exact hB.minj r hr Y ⟨hY, hlt, (not_le.1 hc).le⟩

/-- The light child of the rule is a step that adds one set of size |H|. -/
theorem add_light (hθ : ∀ i, 1 ≤ θ i) (hB : Rule θ k F j H) : AddU θ F {H} H.card where
  ssub := (hB.add_light hθ).ssub
  size := (hB.add_light hθ).size
  pos := (hB.add_light hθ).pos
  deg := by
    intro Y hY hYr
    have h1 := card_over_le hθ hB hB.heart.2.1 hY hYr
    have h2 : (({H} : Finset (Finset α)).filter fun D => Y ⊆ D).card ≤ 1 :=
      (card_le_card (filter_subset _ _)).trans (card_singleton H).le
    have h3 := hθ (H.card - Y.card)
    omega

/-- The heavy child of the rule is a step that adds the petals, of size j − |H|. -/
theorem add_heavy (hθ : ∀ i, 1 ≤ θ i) (hB : Rule θ k F j H) : AddU θ F (petals F j H) (j - H.card) where
  ssub := (hB.add_heavy hθ).ssub
  size := (hB.add_heavy hθ).size
  pos := (hB.add_heavy hθ).pos
  deg := by
    intro Y hY hYr
    have hH := card_pos.2 hB.heart.1
    have hlt := hB.heart.2.1
    have h1 := card_over_le hθ hB (r := j - H.card) (by omega) hY hYr
    have h2 : ((petals F j H).filter fun D => Y ⊆ D).card ≤ θ (j - H.card - Y.card) := by
      rcases hYr.eq_or_lt with he | hYlt
      · exact (card_filter_subset_le_one (fun Q hQ => WidthK.Step.card_of_mem_petals hQ) he).trans (hθ _)
      · by_cases hd : Disjoint H Y
        · have hc : (H ∪ Y).card = H.card + Y.card := card_union_of_disjoint hd
          have hYpos := card_pos.2 hY
          have hlt' : (Sparsify.over F j (H ∪ Y)).card < θ (j - H.card - Y.card) := by
            by_contra hcon
            refine hB.maxH (H ∪ Y) (by omega) ⟨hB.heart.1.mono subset_union_left, by omega, ?_⟩
            rw [hc, show j - (H.card + Y.card) = j - H.card - Y.card by omega]
            exact not_lt.1 hcon
          refine le_trans (le_trans (card_le_card ?_) (card_image_le (f := fun C => C \ H))) hlt'.le
          intro Q hQ
          obtain ⟨hQ, hYQ⟩ := mem_filter.1 hQ
          obtain ⟨C, hC, rfl⟩ := mem_image.1 hQ
          obtain ⟨hCF, hcC, hHC⟩ := mem_filter.1 hC
          exact mem_image.2 ⟨C, mem_filter.2 ⟨hCF, hcC, union_subset hHC (hYQ.trans sdiff_subset)⟩, rfl⟩
        · rw [filter_eq_empty_iff.2]
          · exact Nat.zero_le _
          · intro Q hQ hYQ
            obtain ⟨C, -, rfl⟩ := mem_image.1 hQ
            obtain ⟨x, hxH, hxY⟩ := not_disjoint_iff.1 hd
            exact (mem_sdiff.1 (hYQ hxY)).2 hxH
    omega

variable {τ p t : ℕ} {φ : Finset (Finset α)}

/-- After a step every clause is still a subset of a clause of φ, nonempty if that one is. -/
theorem sub_add {A : Finset (Finset α)} {r : ℕ} (h : ∀ C ∈ F, ∃ C' ∈ φ, C ⊆ C' ∧ (C'.Nonempty → C.Nonempty)) (hA : AddU θ F A r) :
    ∀ C ∈ Sparsify.red (F ∪ A), ∃ C' ∈ φ, C ⊆ C' ∧ (C'.Nonempty → C.Nonempty) := by
  intro C hC
  rcases mem_union.1 (red_subset _ hC) with hC | hC
  · exact h C hC
  · obtain ⟨C₁, hC₁, hCC₁⟩ := hA.ssub C hC
    obtain ⟨C', hC', hsub, -⟩ := h C₁ hC₁
    exact ⟨C', hC', hCC₁.subset.trans hsub, fun _ => by rw [← card_pos, hA.size C hC]; exact hA.pos⟩

/-- The root of the tree of φ is a node with both counters 0. -/
theorem node_root (θ : ℕ → ℕ) (k τ : ℕ) (φ : Finset (Finset α)) : NodeU θ k τ φ (Sparsify.red φ) 0 0 :=
  ⟨fun C hC => ⟨C, red_subset φ hC, Subset.refl _, id⟩, ∅, fun _ => 0, fun _ => 0,
    ⟨reduced_red φ, empty_subset _, by simp [lay], by simp⟩, rfl, by simp, Nat.zero_le _, Nat.zero_le _⟩

/-- The light child counts one more step. -/
theorem node_light (hθ : ∀ i, 1 ≤ θ i) (h : NodeU θ k τ φ F p t) (hB : Rule θ k F j H) :
    NodeU θ k τ φ (light F H) (p + 1) t := by
  have hA := add_light hθ hB
  refine ⟨sub_add h.1 hA, ?_⟩
  obtain ⟨-, N, a, hh, hI, ha0, hh1, hp, ht⟩ := h
  refine ⟨_, _, hh, inv_step hI hA, (WidthK.Step.nextA_zero a hA.pos _).trans ha0, fun r => ?_, ?_, ht⟩
  · exact (hh1 r).trans (Nat.le_add_right _ _)
  · rw [WidthK.Step.sum_nextA_of_lt a _ (lt_of_lt_of_le hB.heart.2.1 hB.le), card_singleton]
    omega

/-- The heavy child counts one more step and adds τ to t. -/
theorem node_heavy (hθ : ∀ i, 1 ≤ θ i) (h : NodeU θ k τ φ F p t) (hB : Rule θ k F j H) :
    NodeU θ k τ φ (heavy F j H) (p + 1) (t + τ) := by
  have hA := add_heavy hθ hB
  have hH := card_pos.2 hB.heart.1
  have hlt := hB.heart.2.1
  have hj := hB.le
  have hr : j - H.card < k := by omega
  have hc : θ (j - H.card) ≤ (petals F j H).card := by rw [card_petals]; exact hB.heart.2.2
  refine ⟨sub_add h.1 hA, ?_⟩
  obtain ⟨-, N, a, hh, hI, ha0, hh1, hp, ht⟩ := h
  refine ⟨_, _, nextA hh (j - H.card) 1, inv_step hI hA, (WidthK.Step.nextA_zero a hA.pos _).trans ha0, fun r => ?_, ?_, ?_⟩
  · have := hh1 r
    simp only [nextA]
    split_ifs with hrr
    · subst hrr
      rw [Nat.add_mul, Nat.one_mul]
      omega
    · simpa only [Nat.add_zero] using this
  · rw [WidthK.Step.sum_nextA_of_lt a _ hr]
    have := hθ (j - H.card)
    omega
  · rw [WidthK.Step.sum_nextA_of_lt hh _ hr, Nat.mul_add, Nat.mul_one]
    omega

end Step

/-- The root of the tree is a node with both counters 0. -/
theorem stNodeRootU : StNodeRootU := fun _ _ θ k τ φ => Step.node_root θ k τ φ

/-- Both children of a node are nodes: one more step, and τ more units at the heavy child. -/
theorem stNodeStepU : StNodeStepU := fun _ _ _ _ _ _ _ _ _ _ _ hθ h hB => ⟨Step.node_light hθ h hB, Step.node_heavy hθ h hB⟩

end UniformInK
