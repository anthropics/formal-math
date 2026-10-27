/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsifyWidthK.Interfaces
import all StepMachines.Math.Sparsify
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-! # The sparsification of a k-CNF on finite sets: one step keeps the invariant, and the final counts

The definitions are in `SparsifyWidthK/Defs.lean`. This file proves four of the interface statements
of `SparsifyWidthK/Interfaces.lean` (the names `St…`).

* `InvK.step`: a step that adds a family A of sets, all of one size r, keeps the invariant `InvK`.
  At size r the degree bound follows from
  `AddK.deg`; at every other size the set N only loses clauses. In the inequality `InvK.acc` the
  sizes below r do not change, size r gains A and loses
  nothing, and a size i above r loses at most |A| · d i clauses, which the right-hand side gains
  through the count at size r.
* `Rule.add_light`, `Rule.add_heavy`: both children of the rule of Impagliazzo, Paturi and Zane are
  such steps.
* `Node.light`, `Node.heavy`: the counters of steps and of heavy steps along a path.
* `Node.bound`, `Leaf.card_le`: the length of a path, the number of its heavy steps, the size of a
  leaf.

Where the argument is the same as for width 3 (the children computed, the clauses of a node, double
counting by `mul_card_le`) the proofs follow
`StepMachines/Math/Sparsify.lean`. That file has two weighted potentials and disjoint petals; the
counts per clause size are particular to this file. -/

namespace WidthK

open Finset Groundwork Groundwork.Sparsify

variable {α : Type*} [DecidableEq α]

namespace Step

variable {d : ℕ → ℕ} {F A N : Finset (Finset α)} {r : ℕ} {a : ℕ → ℕ}

/-- An added set is not a clause of F. -/
theorem notMem (hF : Reduced F) (hA : AddK d F A r) {D : Finset α} (hD : D ∈ A) : D ∉ F := by
  intro hDF
  obtain ⟨C, hC, hDC⟩ := hA.ssub D hD
  exact hDC.ne (hF C hC D hDF hDC.subset)

/-- After a step the minimal clauses are the added ones and the clauses of F that contain none of
them. -/
theorem red_union (hF : Reduced F) (hA : AddK d F A r) :
    Sparsify.red (F ∪ A) = A ∪ F.filter fun C => ∀ D ∈ A, ¬ D ⊆ C := by
  ext C
  simp only [Sparsify.red, mem_filter, mem_union]
  constructor
  · rintro ⟨hC, hmin⟩
    by_cases hCA : C ∈ A
    · exact Or.inl hCA
    · refine Or.inr ⟨hC.resolve_right hCA, fun D hD hDC => hCA ?_⟩
      rw [← hmin D (Or.inr hD) hDC]; exact hD
  · rintro (hCA | ⟨hCF, hno⟩)
    · refine ⟨Or.inr hCA, ?_⟩
      rintro D (hD | hD) hDC
      · obtain ⟨C', hC', hCC'⟩ := hA.ssub C hCA
        have := hF C' hC' D hD (hDC.trans hCC'.subset)
        subst this
        exact absurd hDC hCC'.2
      · exact eq_of_subset_of_card_le hDC (by rw [hA.size C hCA, hA.size D hD])
    · refine ⟨Or.inl hCF, ?_⟩
      rintro D (hD | hD) hDC
      · exact hF C hCF D hD hDC
      · exact absurd hDC (hno D hD)

/-- At a size other than r, N keeps the clauses that contain no added set. -/
theorem lay_nextN_of_ne (hA : AddK d F A r) {i : ℕ} (hi : i ≠ r) :
    lay (nextN N A) i = (lay N i).filter fun C => ∀ D ∈ A, ¬ D ⊆ C := by
  ext C
  simp only [lay, nextN, mem_filter, mem_union]
  constructor
  · rintro ⟨hC | hC, hc⟩
    · exact absurd (hc ▸ hA.size C hC) hi
    · exact ⟨⟨hC.1, hc⟩, hC.2⟩
  · rintro ⟨⟨hC, hc⟩, h⟩
    exact ⟨Or.inr ⟨hC, h⟩, hc⟩

/-- Below size r, N does not change. -/
theorem lay_nextN_of_lt (hA : AddK d F A r) {i : ℕ} (hi : i < r) : lay (nextN N A) i = lay N i := by
  rw [lay_nextN_of_ne hA hi.ne, filter_eq_self]
  intro C hC D hD hDC
  have := card_le_card hDC
  rw [hA.size D hD, (mem_filter.1 hC).2] at this
  omega

/-- At size r, N gains A and loses nothing. -/
theorem lay_nextN_self (hF : Reduced F) (hN : N ⊆ F) (hA : AddK d F A r) : lay (nextN N A) r = A ∪ lay N r := by
  ext C
  simp only [lay, nextN, mem_filter, mem_union]
  constructor
  · rintro ⟨hC | hC, hc⟩
    · exact Or.inl hC
    · exact Or.inr ⟨hC.1, hc⟩
  · rintro (hC | ⟨hC, hc⟩)
    · exact ⟨Or.inl hC, hA.size C hC⟩
    · refine ⟨Or.inr ⟨hC, fun D hD hDC => ?_⟩, hc⟩
      have : D = C := eq_of_subset_of_card_le hDC (by rw [hc, hA.size D hD])
      exact notMem hF hA hD (this ▸ hN hC)

/-- The counts below size i do not change if i ≤ r. -/
theorem sum_nextA_of_le (a : ℕ → ℕ) (c : ℕ) {i r : ℕ} (hi : i ≤ r) :
    ∑ i' ∈ range i, nextA a r c i' = ∑ i' ∈ range i, a i' := by
  refine sum_congr rfl fun i' hi' => ?_
  have := mem_range.1 hi'
  simp only [nextA, if_neg (show i' ≠ r by omega), Nat.add_zero]

/-- The counts below size i grow by c in total if r < i. -/
theorem sum_nextA_of_lt (a : ℕ → ℕ) (c : ℕ) {i r : ℕ} (hi : r < i) :
    ∑ i' ∈ range i, nextA a r c i' = ∑ i' ∈ range i, a i' + c := by
  simp only [nextA, sum_add_distrib, sum_ite_eq', mem_range, if_pos hi]

/-- A step removes at most |A| · d i clauses of size i from N. -/
theorem card_lay_le (h : InvK d F N a) (hA : AddK d F A r) (i : ℕ) :
    (lay N i).card ≤ ((lay N i).filter fun C => ∀ D ∈ A, ¬ D ⊆ C).card + A.card * d i := by
  have hsplit := card_filter_add_card_filter_not (s := lay N i) (fun C => ∀ D ∈ A, ¬ D ⊆ C)
  have hle : ((lay N i).filter fun C => ¬ ∀ D ∈ A, ¬ D ⊆ C).card ≤ A.card * d i := by
    refine le_trans (card_le_card ?_) (card_biUnion_le_card_mul A (fun D => (lay N i).filter fun C => D ⊆ C) (d i) ?_)
    · intro C hC
      obtain ⟨hCN, hex⟩ := mem_filter.1 hC
      simp only [not_forall, not_not] at hex
      obtain ⟨D, hD, hDC⟩ := hex
      exact mem_biUnion.2 ⟨D, hD, mem_filter.2 ⟨hCN, hDC⟩⟩
    · intro D hD
      obtain ⟨y, hy⟩ : D.Nonempty := by rw [← card_pos, hA.size D hD]; exact hA.pos
      refine (card_le_card fun C hC => ?_).trans (h.deg i y)
      obtain ⟨hCN, hDC⟩ := mem_filter.1 hC
      exact mem_filter.2 ⟨hCN, hDC hy⟩
  omega

end Step

open Step

section StepLemma

variable {d : ℕ → ℕ} {F A N : Finset (Finset α)} {r : ℕ} {a : ℕ → ℕ}

/-- A step that adds A, all of size r, keeps the invariant: N becomes `nextN N A`, and the count at
size r grows by |A|. -/
public theorem InvK.step (h : InvK d F N a) (hA : AddK d F A r) :
    InvK d (Sparsify.red (F ∪ A)) (nextN N A) (nextA a r A.card) where
  red := reduced_red _
  sub := by
    rw [red_union h.red hA]
    exact union_subset_union_right (filter_subset_filter _ h.sub)
  deg := by
    intro i y
    by_cases hi : i = r
    · subst hi
      rw [lay_nextN_self h.red h.sub hA, filter_union]
      have h1 : ((lay N i).filter fun C => y ∈ C).card ≤ (Sparsify.over F i {y}).card := by
        apply card_le_card
        intro C hC
        obtain ⟨hCN, hyC⟩ := mem_filter.1 hC
        obtain ⟨hCN, hc⟩ := mem_filter.1 hCN
        exact mem_filter.2 ⟨h.sub hCN, hc, singleton_subset_iff.2 hyC⟩
      have := card_union_le (A.filter fun C => y ∈ C) ((lay N i).filter fun C => y ∈ C)
      have := hA.deg y
      omega
    · rw [lay_nextN_of_ne hA hi]
      exact (card_le_card (filter_subset_filter _ (filter_subset _ _))).trans (h.deg i y)
  acc := by
    intro i
    rcases lt_trichotomy i r with hi | hi | hi
    · rw [lay_nextN_of_lt hA hi, sum_nextA_of_le a _ hi.le]
      simpa only [nextA, if_neg hi.ne, Nat.add_zero] using h.acc i
    · subst hi
      rw [lay_nextN_self h.red h.sub hA, sum_nextA_of_le a _ le_rfl, card_union_of_disjoint]
      · have := h.acc i
        simp only [nextA, if_true]
        omega
      · rw [disjoint_left]
        intro C hCA hCN
        exact notMem h.red hA hCA (h.sub (mem_filter.1 hCN).1)
    · rw [lay_nextN_of_ne hA hi.ne', sum_nextA_of_lt a _ hi]
      have h1 := h.acc i
      have h2 := card_lay_le h hA i
      simp only [nextA, if_neg hi.ne', Nat.add_zero, Nat.mul_add]
      rw [Nat.mul_comm (d i) A.card]
      omega

end StepLemma

variable {θ : ℕ → ℕ} {k j : ℕ} {F : Finset (Finset α)} {H : Finset α}

namespace Step

/-- A literal lies in at most one set of size 1. -/
theorem card_filter_mem_le_one {G : Finset (Finset α)} (hG : ∀ C ∈ G, C.card = 1) (y : α) :
    (G.filter fun C => y ∈ C).card ≤ 1 := by
  rw [card_le_one]
  intro C hC D hD
  obtain ⟨hC, hyC⟩ := mem_filter.1 hC
  obtain ⟨hD, hyD⟩ := mem_filter.1 hD
  obtain ⟨c, rfl⟩ := card_eq_one.1 (hG C hC)
  obtain ⟨e, rfl⟩ := card_eq_one.1 (hG D hD)
  rw [mem_singleton] at hyC hyD
  rw [← hyC, ← hyD]

/-- Below the size j of the rule every literal lies in at most θ s clauses of size s + 1. -/
theorem card_over_le (hθ : ∀ i, 0 < θ i) (hB : Rule θ k F j H) {s : ℕ} (hs : s + 1 < j) (y : α) :
    (Sparsify.over F (s + 1) {y}).card ≤ θ s := by
  rcases Nat.eq_zero_or_pos s with rfl | h1
  · refine le_trans ?_ (hθ _)
    have := card_filter_mem_le_one (G := F.filter fun C => C.card = 1) (fun C hC => (mem_filter.1 hC).2) y
    simpa only [Sparsify.over, filter_filter, singleton_subset_iff] using this
  · by_contra hc
    refine hB.minj (s + 1) hs {y} ⟨singleton_nonempty y, by rw [card_singleton]; omega, ?_⟩
    rw [card_singleton, Nat.add_sub_cancel]
    exact (not_le.1 hc).le

/-- Some clause of size j contains the heart. -/
theorem exists_over (hθ : ∀ i, 0 < θ i) (hB : Rule θ k F j H) : ∃ C, C ∈ Sparsify.over F j H :=
  card_pos.1 (lt_of_lt_of_le (hθ _) hB.heart.2.2)

/-- Every petal has size j - |H|. -/
theorem card_of_mem_petals {Q : Finset α} (hQ : Q ∈ petals F j H) : Q.card = j - H.card := by
  obtain ⟨C, hC, rfl⟩ := mem_image.1 hQ
  obtain ⟨-, hc, hHC⟩ := mem_filter.1 hC
  rw [card_sdiff_of_subset hHC, hc]

end Step

/-- There are as many petals as clauses of size j over H. -/
public theorem card_petals (F : Finset (Finset α)) (j : ℕ) (H : Finset α) :
    (petals F j H).card = (Sparsify.over F j H).card := by
  refine card_image_of_injOn ?_
  intro C hC D hD hCD
  have hHC := (mem_filter.1 (mem_coe.1 hC)).2.2
  have hHD := (mem_filter.1 (mem_coe.1 hD)).2.2
  have hCD' : C \ H = D \ H := hCD
  rw [← sdiff_union_of_subset hHC, ← sdiff_union_of_subset hHD, hCD']

/-- The light child of the rule is a step that adds one set of size |H|. -/
public theorem Rule.add_light (hθ : ∀ i, 0 < θ i) (hB : Rule θ k F j H) : AddK (dg θ) F {H} H.card where
  ssub := by
    intro D hD
    obtain rfl := mem_singleton.1 hD
    obtain ⟨C, hC⟩ := exists_over hθ hB
    obtain ⟨hCF, hc, hDC⟩ := mem_filter.1 hC
    refine ⟨C, hCF, hDC, fun hsub => ?_⟩
    have := card_le_card hsub
    have := hB.heart.2.1
    omega
  size := fun D hD => by rw [mem_singleton.1 hD]
  pos := card_pos.2 hB.heart.1
  deg := by
    intro y
    obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero (card_pos.2 hB.heart.1).ne'
    have hlt := hB.heart.2.1
    rw [hs]
    have h1 := card_over_le hθ hB (s := s) (by omega) y
    have h2 : (({H} : Finset (Finset α)).filter fun D => y ∈ D).card ≤ 1 :=
      (card_le_card (filter_subset _ _)).trans (card_singleton H).le
    have h3 := hθ s
    simp only [dg, Nat.succ_eq_add_one]
    omega

/-- The heavy child of the rule is a step that adds the petals, of size j - |H|. -/
public theorem Rule.add_heavy (hθ : ∀ i, 0 < θ i) (hB : Rule θ k F j H) :
    AddK (dg θ) F (petals F j H) (j - H.card) where
  ssub := by
    intro Q hQ
    obtain ⟨C, hC, rfl⟩ := mem_image.1 hQ
    obtain ⟨hCF, -, hHC⟩ := mem_filter.1 hC
    refine ⟨C, hCF, sdiff_subset, fun hsub => ?_⟩
    obtain ⟨x, hx⟩ := hB.heart.1
    exact (mem_sdiff.1 (hsub (hHC hx))).2 hx
  size := fun Q hQ => card_of_mem_petals hQ
  pos := Nat.sub_pos_of_lt hB.heart.2.1
  deg := by
    intro y
    have hH := card_pos.2 hB.heart.1
    have hlt := hB.heart.2.1
    obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.sub_pos_of_lt hlt).ne'
    have h2 : ((petals F j H).filter fun D => y ∈ D).card ≤ θ s := by
      rcases Nat.eq_zero_or_pos s with rfl | hs0
      · exact (card_filter_mem_le_one (fun Q hQ => (card_of_mem_petals hQ).trans hs) y).trans (hθ _)
      · by_cases hy : y ∈ H
        · rw [filter_eq_empty_iff.2]
          · exact Nat.zero_le _
          · intro Q hQ hyQ
            obtain ⟨C, -, rfl⟩ := mem_image.1 hQ
            exact (mem_sdiff.1 hyQ).2 hy
        · have hc : (insert y H).card = H.card + 1 := card_insert_of_notMem hy
          have hlt' : (Sparsify.over F j (insert y H)).card < θ s := by
            by_contra hcon
            refine hB.maxH (insert y H) (by omega) ⟨insert_nonempty y H, by omega, ?_⟩
            rw [hc, show j - (H.card + 1) = s by omega]
            exact not_lt.1 hcon
          refine le_trans (le_trans (card_le_card ?_) (card_image_le (f := fun C => C \ H))) hlt'.le
          intro Q hQ
          obtain ⟨hQ, hyQ⟩ := mem_filter.1 hQ
          obtain ⟨C, hC, rfl⟩ := mem_image.1 hQ
          obtain ⟨hCF, hcC, hHC⟩ := mem_filter.1 hC
          exact mem_image.2 ⟨C, mem_filter.2 ⟨hCF, hcC, insert_subset (mem_sdiff.1 hyQ).1 hHC⟩, rfl⟩
    rw [hs]
    have h1 := card_over_le hθ hB (s := s) (by omega) y
    simp only [dg, Nat.succ_eq_add_one]
    omega

variable {τ p t : ℕ} {φ : Finset (Finset α)}

namespace Step

/-- After a step every clause is still a subset of a clause of φ, nonempty if that one is. -/
theorem sub_add {d : ℕ → ℕ} {A : Finset (Finset α)} {r : ℕ} (h : Node θ k τ φ F p t) (hA : AddK d F A r) :
    ∀ C ∈ Sparsify.red (F ∪ A), ∃ C' ∈ φ, C ⊆ C' ∧ (C'.Nonempty → C.Nonempty) := by
  intro C hC
  rcases mem_union.1 (red_subset _ hC) with hC | hC
  · exact h.1 C hC
  · obtain ⟨C₁, hC₁, hCC₁⟩ := hA.ssub C hC
    obtain ⟨C', hC', hsub, -⟩ := h.1 C₁ hC₁
    exact ⟨C', hC', hCC₁.subset.trans hsub, fun _ => by rw [← card_pos, hA.size C hC]; exact hA.pos⟩

/-- The count at size 0 does not change. -/
theorem nextA_zero (a : ℕ → ℕ) {r : ℕ} (hr : 0 < r) (c : ℕ) : nextA a r c 0 = a 0 := by
  simp only [nextA, if_neg hr.ne, Nat.add_zero]

end Step

/-- The root of the tree of φ is a node with both counters 0. -/
public theorem node_root (θ : ℕ → ℕ) (k τ : ℕ) (φ : Finset (Finset α)) : Node θ k τ φ (Sparsify.red φ) 0 0 :=
  ⟨fun C hC => ⟨C, red_subset φ hC, Subset.refl _, id⟩, ∅, fun _ => 0, fun _ => 0,
    ⟨reduced_red φ, empty_subset _, by simp [lay], by simp⟩, rfl, by simp, Nat.zero_le _, Nat.zero_le _⟩

/-- The light child counts one more step. -/
public theorem Node.light (hθ : ∀ i, 0 < θ i) (h : Node θ k τ φ F p t) (hB : Rule θ k F j H) :
    Node θ k τ φ (light F H) (p + 1) t := by
  have hA := hB.add_light hθ
  refine ⟨sub_add h hA, ?_⟩
  obtain ⟨-, N, a, hh, hI, ha0, hh1, hp, ht⟩ := h
  refine ⟨_, _, hh, hI.step hA, (nextA_zero a hA.pos _).trans ha0, fun r => ?_, ?_, ht⟩
  · exact (hh1 r).trans (Nat.le_add_right _ _)
  · rw [sum_nextA_of_lt a _ (lt_of_lt_of_le hB.heart.2.1 hB.le), card_singleton]
    omega

/-- The heavy child counts one more step and adds τ to t. -/
public theorem Node.heavy (hθ : ∀ i, 0 < θ i) (h : Node θ k τ φ F p t) (hB : Rule θ k F j H) :
    Node θ k τ φ (heavy F j H) (p + 1) (t + τ) := by
  have hA := hB.add_heavy hθ
  have hH := card_pos.2 hB.heart.1
  have hlt := hB.heart.2.1
  have hj := hB.le
  have hr : j - H.card < k := by omega
  have hc : θ (j - H.card) ≤ (petals F j H).card := by rw [card_petals]; exact hB.heart.2.2
  refine ⟨sub_add h hA, ?_⟩
  obtain ⟨-, N, a, hh, hI, ha0, hh1, hp, ht⟩ := h
  refine ⟨_, _, nextA hh (j - H.card) 1, hI.step hA, (nextA_zero a hA.pos _).trans ha0, fun r => ?_, ?_, ?_⟩
  · have := hh1 r
    simp only [nextA]
    split_ifs with hrr
    · subst hrr
      rw [Nat.add_mul, Nat.one_mul]
      omega
    · simpa only [Nat.add_zero] using this
  · rw [sum_nextA_of_lt a _ hr]
    have := hθ (j - H.card)
    omega
  · rw [sum_nextA_of_lt hh _ hr, Nat.mul_add, Nat.mul_one]
    omega

section Count

variable {n : ℕ} {U : Finset α} {β : ℕ → ℕ}

/-- At most β i · n clauses of size i are added along a path. U: the at most 2n literals. -/
theorem Step.acc_le {d : ℕ → ℕ} {N : Finset (Finset α)} {a : ℕ → ℕ} (hU : U.card ≤ 2 * n) (hFU : ∀ C ∈ F, C ⊆ U)
    (h : InvK d F N a) (ha0 : a 0 = 0) (hβ : ∀ i, 0 < i → d i * (2 + ∑ i' ∈ range i, β i') ≤ β i) (i : ℕ) :
    a i ≤ β i * n := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [ha0]; exact Nat.zero_le _
    have h1 : (lay N i).card ≤ 2 * n * d i := by
      have := mul_card_le U (lay N i) i (d i) (fun C hC => hFU C (h.sub (mem_filter.1 hC).1))
        (fun C hC => (mem_filter.1 hC).2) (h.deg i)
      calc (lay N i).card ≤ i * (lay N i).card := Nat.le_mul_of_pos_left _ hi
        _ ≤ U.card * d i := this
        _ ≤ 2 * n * d i := Nat.mul_le_mul_right _ hU
    have h2 : ∑ i' ∈ range i, a i' ≤ (∑ i' ∈ range i, β i') * n := by
      rw [sum_mul]
      exact sum_le_sum fun i' hi' => ih i' (mem_range.1 hi')
    calc a i ≤ (lay N i).card + d i * ∑ i' ∈ range i, a i' := h.acc i
      _ ≤ 2 * n * d i + d i * ((∑ i' ∈ range i, β i') * n) := Nat.add_le_add h1 (Nat.mul_le_mul_left _ h2)
      _ = d i * (2 + ∑ i' ∈ range i, β i') * n := by ring
      _ ≤ β i * n := Nat.mul_le_mul_right _ (hβ i hi)

/-- If the clauses of φ are subsets of U, so are the clauses of every node. -/
public theorem Node.subset_of (hφ : ∀ C ∈ φ, C ⊆ U) (h : Node θ k τ φ F p t) : ∀ C ∈ F, C ⊆ U := by
  intro C hC
  obtain ⟨C', hC', hsub, -⟩ := h.1 C hC
  exact hsub.trans (hφ C' hC')

/-- A path has at most (β 0 + … + β (k-1)) · n steps, and its heavy steps use at most k · n units, τ
each. -/
public theorem Node.bound (hT : Thr τ θ β) (hU : U.card ≤ 2 * n) (hφ : ∀ C ∈ φ, C ⊆ U) (h : Node θ k τ φ F p t) :
    p ≤ (∑ i ∈ range k, β i) * n ∧ t ≤ k * n := by
  have hFU := h.subset_of hφ
  obtain ⟨-, N, a, hh, hI, ha0, hh1, hp, ht⟩ := h
  have ha := acc_le hU hFU hI ha0 (β := β) fun i hi => by
    obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi.ne'
    exact hT.step i
  constructor
  · rw [sum_mul]
    exact hp.trans (sum_le_sum fun i _ => ha i)
  · refine ht.trans ?_
    rw [mul_sum]
    refine (sum_le_card_nsmul _ _ n fun r _ => ?_).trans (by simp)
    have h1 : τ * hh r * β r ≤ n * β r := by
      calc τ * hh r * β r = hh r * (τ * β r) := by ring
        _ ≤ hh r * θ r := Nat.mul_le_mul_left _ (hT.mul r)
        _ ≤ a r := hh1 r
        _ ≤ β r * n := ha r
        _ = n * β r := Nat.mul_comm _ _
    rcases Nat.eq_zero_or_pos (β r) with h0 | h0
    · have h2 := (hh1 r).trans (ha r)
      rw [h0, Nat.zero_mul] at h2
      have h3 : hh r = 0 := by
        rcases Nat.eq_zero_or_pos (hh r) with h | h
        · exact h
        · exact absurd (Nat.mul_pos h (hT.pos r)) (by omega)
      rw [h3, Nat.mul_zero]; exact Nat.zero_le _
    · exact Nat.le_of_mul_le_mul_right h1 h0

/-- A leaf has at most 2n · (θ 0 + … + θ (k-1)) clauses. -/
public theorem Leaf.card_le (hθ : ∀ i, 0 < θ i) (hU : U.card ≤ 2 * n) (hFU : ∀ C ∈ F, C ⊆ U) (h : Leaf θ k F)
    (hF : ∀ C ∈ F, 1 ≤ C.card ∧ C.card ≤ k) : F.card ≤ 2 * n * ∑ i ∈ range k, θ i := by
  have hlay : ∀ i < k, (lay F (i + 1)).card ≤ 2 * n * θ i := by
    intro i hi
    have hd : ∀ y, ((lay F (i + 1)).filter fun C => y ∈ C).card ≤ θ i := by
      intro y
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · exact (card_filter_mem_le_one (fun C hC => (mem_filter.1 hC).2) y).trans (hθ 0)
      · by_contra hc
        refine h (i + 1) hi {y} ⟨singleton_nonempty y, by rw [card_singleton]; omega, ?_⟩
        rw [card_singleton, Nat.add_sub_cancel]
        simpa only [lay, Sparsify.over, filter_filter, singleton_subset_iff] using (not_le.1 hc).le
    have := mul_card_le U (lay F (i + 1)) (i + 1) (θ i) (fun C hC => hFU C (mem_filter.1 hC).1)
      (fun C hC => (mem_filter.1 hC).2) hd
    calc (lay F (i + 1)).card ≤ (i + 1) * (lay F (i + 1)).card := Nat.le_mul_of_pos_left _ (Nat.succ_pos i)
      _ ≤ U.card * θ i := this
      _ ≤ 2 * n * θ i := Nat.mul_le_mul_right _ hU
  have hsub : F ⊆ (range k).biUnion fun i => lay F (i + 1) := by
    intro C hC
    obtain ⟨h1, h2⟩ := hF C hC
    exact mem_biUnion.2 ⟨C.card - 1, mem_range.2 (by omega), mem_filter.2 ⟨hC, by omega⟩⟩
  calc F.card ≤ ((range k).biUnion fun i => lay F (i + 1)).card := card_le_card hsub
    _ ≤ ∑ i ∈ range k, (lay F (i + 1)).card := card_biUnion_le
    _ ≤ ∑ i ∈ range k, 2 * n * θ i := sum_le_sum fun i hi => hlay i (mem_range.1 hi)
    _ = 2 * n * ∑ i ∈ range k, θ i := by rw [mul_sum]

end Count

/-! ### The interface statements of `SparsifyWidthK/Interfaces.lean` proved by this file -/

/-- `node_root`, in the form of the interface. -/
public theorem stNodeRoot : StNodeRoot := fun _ _ θ k τ φ => node_root θ k τ φ

/-- `Node.light` and `Node.heavy`, in the form of the interface. -/
public theorem stNodeStep : StNodeStep := fun _ _ _ _ _ _ _ _ _ _ _ hθ h hB => ⟨h.light hθ hB, h.heavy hθ hB⟩

/-- `Node.bound`, in the form of the interface. -/
public theorem stNodeBound : StNodeBound := fun _ _ _ _ _ _ _ _ _ _ _ _ hT hU hφ h => h.bound hT hU hφ

/-- `Leaf.card_le`, in the form of the interface. -/
public theorem stLeafCard : StLeafCard := by
  intro α _ θ k n F U hθ hU hF h
  have := h.card_le hθ hU (fun C hC => (hF C hC).1) fun C hC => ⟨card_pos.2 (hF C hC).2.1, (hF C hC).2.2⟩
  calc F.card ≤ 2 * n * ∑ i ∈ range k, θ i := this
    _ = (2 * ∑ j ∈ range k, θ j) * n := by ring

end WidthK
