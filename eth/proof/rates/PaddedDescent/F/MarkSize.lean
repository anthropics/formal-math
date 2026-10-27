/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.Interfaces
import PaddedDescent.F.MarkDeg
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Marks and layers: the size of the network of an admissible profile

This file proves the interface statement `StMarkSized` of
proof/rates/PaddedDescent/F/Interfaces.lean (`stMarkSized`): the network `markN` of an admissible
profile has size
`Pb`, entries 0, 1, −1, and at most `Ub` shared bits. The clauses come as a list `Ls` of layers,
each a list of clauses, and a profile prescribes its numbers of set marks layer by layer.
Two counts carry the proof. A clause touches a chain of nodes, so at one node it has at most two
links (`card_links_at_le`), and with at most k literals at most k − 1 links in all
(`card_links_le`). An admissible profile prescribes at
most as many set marks as two nodes compare, and at most (k − 1)·w set marks in a layer; together
with the length of the code of a label this bounds the capacities at a
node (`sum_mcap_le`) and their sum (`U_markN_le`). That at most qv g n · Δ clauses touch a node is
`Deg.length_tch_le_of_wfL` of proof/rates/PaddedDescent/F/MarkDeg.lean. -/

namespace PaddedDescent.F.Mark.Size

open Groundwork Groundwork.Prog Finset

/-! ### The links of a clause -/

variable {g n : ℕ} {Ls : List Fml}

/-- a and b are neighbours in the chain of clause e exactly when a < b, e touches both, and e
touches no node between them. -/
theorem linkB_iff {e a b : ℕ} : linkB g n Ls e a b = true ↔
    a < b ∧ tchB g n Ls a e = true ∧ tchB g n Ls b e = true ∧ ∀ c < g, a < c → c < b → tchB g n Ls c e = false := by
  simp only [linkB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_false_iff_not]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨h1, h2, h3, fun c hc hac hcb => ?_⟩
    rcases h4 c hc with (h | h) | h
    · exact absurd hac h
    · exact absurd hcb h
    · exact h
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨⟨h1, h2⟩, h3⟩, fun c hc => ?_⟩
    by_cases hac : a < c
    · by_cases hcb : c < b
      · exact Or.inr (h4 c hc hac hcb)
      · exact Or.inl (Or.inr hcb)
    · exact Or.inl (Or.inl hac)

/-- The upper end of a link determines its lower end. -/
theorem link_left_unique {e a a' b : ℕ} (hb : b ≤ g) (h : linkB g n Ls e a b = true) (h' : linkB g n Ls e a' b = true) : a = a' := by
  obtain ⟨h1, h2, -, h4⟩ := linkB_iff.1 h
  obtain ⟨h1', h2', -, h4'⟩ := linkB_iff.1 h'
  rcases lt_trichotomy a a' with hlt | heq | hgt
  · have := h4 a' (by omega) hlt h1'; rw [h2'] at this; exact absurd this (by simp)
  · exact heq
  · have := h4' a (by omega) hgt h1; rw [h2] at this; exact absurd this (by simp)

/-- The lower end of a link determines its upper end. -/
theorem link_right_unique {e a b b' : ℕ} (hb : b < g) (hb' : b' < g) (h : linkB g n Ls e a b = true) (h' : linkB g n Ls e a b' = true) : b = b' := by
  obtain ⟨h1, -, h3, h4⟩ := linkB_iff.1 h
  obtain ⟨h1', -, h3', h4'⟩ := linkB_iff.1 h'
  rcases lt_trichotomy b b' with hlt | heq | hgt
  · have := h4' b hb h1 hlt; rw [h3] at this; exact absurd this (by simp)
  · exact heq
  · have := h4 b' hb' h1' hgt; rw [h3'] at this; exact absurd this (by simp)

/-- The number of nodes that a clause touches is at most its number of literals. -/
theorem card_touched_le (e : ℕ) : #((range g).filter fun a => tchB g n Ls a e = true) ≤ (clAt Ls e).2.length := by
  have hsub : ((range g).filter fun a => tchB g n Ls a e = true) ⊆ ((clAt Ls e).2.map fun l => l.1 / qv g n).toFinset := by
    intro a ha
    have h := (mem_filter.1 ha).2
    simp only [tchB, List.any_eq_true, beq_iff_eq] at h
    obtain ⟨l, hl, rfl⟩ := h
    exact List.mem_toFinset.2 (List.mem_map.2 ⟨l, hl, rfl⟩)
  exact (card_le_card hsub).trans ((List.toFinset_card_le _).trans (by simp))

/-- A clause that touches a node has fewer links than touched nodes. -/
theorem card_links_lt (e : ℕ) (h : ∃ a < g, tchB g n Ls a e = true) :
    #(((range g) ×ˢ (range g)).filter fun p => linkB g n Ls e p.1 p.2 = true) < #((range g).filter fun a => tchB g n Ls a e = true) := by
  classical
  -- the least touched node is the upper end of no link
  obtain ⟨a₀, ha₀, hmin⟩ : ∃ a₀ ∈ (range g).filter (fun a => tchB g n Ls a e = true),
      ∀ a ∈ (range g).filter (fun a => tchB g n Ls a e = true), a₀ ≤ a := by
    obtain ⟨a, ha, ht⟩ := h
    exact exists_min_image _ id ⟨a, mem_filter.2 ⟨mem_range.2 ha, ht⟩⟩
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.2) (((range g) ×ˢ (range g)).filter fun p => linkB g n Ls e p.1 p.2 = true : Finset (ℕ × ℕ)) := by
    rintro ⟨a, b⟩ hp ⟨a', b'⟩ hp' (hbb : b = b')
    subst hbb
    have h1 := mem_filter.1 (mem_coe.1 hp)
    have h2 := mem_filter.1 (mem_coe.1 hp')
    have hb : b < g := mem_range.1 (mem_product.1 h1.1).2
    have haa : a = a' := link_left_unique hb.le h1.2 h2.2
    rw [haa]
  rw [← card_image_of_injOn hinj]
  refine card_lt_card ⟨?_, fun hsub => ?_⟩
  · intro b hb
    obtain ⟨⟨a, b'⟩, hp, rfl⟩ := mem_image.1 hb
    have h1 := mem_filter.1 hp
    exact mem_filter.2 ⟨(mem_product.1 h1.1).2, (linkB_iff.1 h1.2).2.2.1⟩
  · obtain ⟨⟨a, b⟩, hp, (hb : b = a₀)⟩ := mem_image.1 (hsub ha₀)
    subst hb
    have h1 := mem_filter.1 hp
    obtain ⟨hab, hta, -, -⟩ := linkB_iff.1 h1.2
    have := hmin a (mem_filter.2 ⟨(mem_product.1 h1.1).1, hta⟩)
    omega

/-- The length of a filtered list of the numbers below M, as the number of elements of a finite set. -/
theorem length_filter_eq_card (M : ℕ) (p : ℕ → Bool) : ((List.range M).filter p).length = #((range M).filter fun e => p e = true) := by
  rw [← List.toFinset_card_of_nodup (List.nodup_range.filter _)]
  congr 1
  ext e
  simp

/-- The list `cls` holds as many entries of layer i as layer i has clauses. -/
theorem countP_cls (Ls : List Fml) (i : ℕ) : (cls Ls).countP (fun c => c.1 == i) = (Ls.getD i []).length := by
  have key : ∀ (l : List ℕ), l.Nodup → ((l.flatMap fun j => (Ls.getD j []).map fun C => (j, C)).countP fun c => c.1 == i) =
      if i ∈ l then (Ls.getD i []).length else 0 := by
    intro l
    induction l with
    | nil => simp
    | cons j l ih =>
      intro hnd
      rw [List.flatMap_cons, List.countP_append, ih (List.nodup_cons.1 hnd).2, List.countP_map]
      by_cases hji : j = i
      · subst hji
        have : j ∉ l := (List.nodup_cons.1 hnd).1
        simp [this, Function.comp_def]
      · have h1 : ((fun c : ℕ × Cl => c.1 == i) ∘ fun C => (j, C)) = fun _ => false := by
          funext C; simp [hji]
        rw [h1]
        simp [Ne.symm hji]
  rw [cls, key _ List.nodup_range]
  by_cases hi : i < Ls.length
  · simp [hi]
  · simp [hi, List.getD_eq_getElem?_getD]

/-- A clause of k literals has at most k − 1 links, and an empty clause has none. -/
theorem card_links_le (e : ℕ) :
    #(((range g) ×ˢ (range g)).filter fun p => linkB g n Ls e p.1 p.2 = true) ≤ (clAt Ls e).2.length - 1 := by
  by_cases h : ∃ a < g, tchB g n Ls a e = true
  · have := card_links_lt e h
    have := card_touched_le (g := g) (n := n) (Ls := Ls) e
    omega
  · rw [card_eq_zero.2]
    · exact Nat.zero_le _
    · refine filter_eq_empty_iff.2 fun p hp hl => h ⟨p.1, mem_range.1 (mem_product.1 hp).1, (linkB_iff.1 hl).2.1⟩

/-- All the strings of layer i together have at most k − 1 bits for each clause of the layer, if the
clauses have at most k literals. -/
theorem sum_length_tst_le (k i : ℕ) (hk : ∀ C ∈ Ls.getD i [], C.length ≤ k) :
    ∑ p ∈ (range g) ×ˢ (range g), (if p.1 < p.2 then (tst g n Ls p.1 p.2 i).length else 0) ≤ (k - 1) * (Ls.getD i []).length := by
  have h1 : ∀ p : ℕ × ℕ, (if p.1 < p.2 then (tst g n Ls p.1 p.2 i).length else 0) =
      ∑ e ∈ range (cls Ls).length, if (clAt Ls e).1 = i ∧ linkB g n Ls e p.1 p.2 = true then 1 else 0 := by
    intro p
    rw [← card_filter]
    split_ifs with hp
    · rw [tst, length_filter_eq_card, min_eq_left hp.le, max_eq_right hp.le]
      congr 1
      ext e
      simp
    · symm
      exact card_eq_zero.2 (filter_eq_empty_iff.2 fun e _ he => hp (linkB_iff.1 he.2).1)
  rw [sum_congr rfl fun p _ => h1 p, sum_comm]
  have h2 : ∀ e ∈ range (cls Ls).length, (∑ p ∈ (range g) ×ˢ (range g), if (clAt Ls e).1 = i ∧ linkB g n Ls e p.1 p.2 = true then 1 else 0) ≤
      if (clAt Ls e).1 = i then k - 1 else 0 := by
    intro e he
    split_ifs with hi
    · simp only [hi, true_and]
      rw [← card_filter]
      refine (card_links_le e).trans (Nat.sub_le_sub_right (hk _ ?_) 1)
      have hm : clAt Ls e ∈ cls Ls := by
        rw [clAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (mem_range.1 he), Option.getD_some]
        exact List.getElem_mem _
      obtain ⟨j, -, hj⟩ := List.mem_flatMap.1 hm
      obtain ⟨C, hC, hCe⟩ := List.mem_map.1 hj
      rw [← hCe] at hi ⊢
      exact hi ▸ hC
    · simp [hi]
  refine (sum_le_sum h2).trans ?_
  rw [← sum_filter, sum_const, smul_eq_mul, Nat.mul_comm]
  refine Nat.mul_le_mul_left _ (le_of_eq ?_)
  rw [← countP_cls, ← Deg.length_filter_range (cls Ls) (0, []) fun c => c.1 == i, length_filter_eq_card]
  congr 1
  ext e
  simp [clAt]

/-- At a node a, a clause has at most two links, and none if it does not touch a. -/
theorem card_links_at_le {a : ℕ} (ha : a < g) (e : ℕ) :
    #(((range g).erase a).filter fun b => linkB g n Ls e (min a b) (max a b) = true) ≤ if tchB g n Ls a e = true then 2 else 0 := by
  classical
  split_ifs with ht
  · have hsub : (((range g).erase a).filter fun b => linkB g n Ls e (min a b) (max a b) = true) ⊆
        ((range g).filter fun b => linkB g n Ls e b a = true) ∪ ((range g).filter fun b => linkB g n Ls e a b = true) := by
      intro b hb
      obtain ⟨hb1, hb2⟩ := mem_filter.1 hb
      obtain ⟨hne, hbg⟩ := mem_erase.1 hb1
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [min_eq_right hlt.le, max_eq_left hlt.le] at hb2
        exact mem_union_left _ (mem_filter.2 ⟨hbg, hb2⟩)
      · rw [min_eq_left hgt.le, max_eq_right hgt.le] at hb2
        exact mem_union_right _ (mem_filter.2 ⟨hbg, hb2⟩)
    have c1 : #((range g).filter fun b => linkB g n Ls e b a = true) ≤ 1 :=
      card_le_one.2 fun b hb b' hb' => link_left_unique ha.le (mem_filter.1 hb).2 (mem_filter.1 hb').2
    have c2 : #((range g).filter fun b => linkB g n Ls e a b = true) ≤ 1 :=
      card_le_one.2 fun b hb b' hb' => link_right_unique (mem_range.1 (mem_filter.1 hb).1) (mem_range.1 (mem_filter.1 hb').1)
        (mem_filter.1 hb).2 (mem_filter.1 hb').2
    exact (card_le_card hsub).trans ((card_union_le _ _).trans (by omega))
  · refine le_of_eq (card_eq_zero.2 (filter_eq_empty_iff.2 fun b _ hl => ht ?_))
    obtain ⟨-, h2, h3, -⟩ := linkB_iff.1 hl
    rcases le_total a b with h | h
    · rwa [min_eq_left h] at h2
    · rwa [max_eq_left h] at h3

/-- All the strings that a node a shares with the other nodes together have at most twice as many
bits as clauses touch a. -/
theorem sum_length_tst_node_le {a : ℕ} (ha : a < g) :
    ∑ b ∈ (range g).erase a, ∑ i ∈ range Ls.length, (tst g n Ls a b i).length ≤ 2 * (tch g n Ls a).length := by
  have h1 : ∀ b i : ℕ, (tst g n Ls a b i).length =
      ∑ e ∈ range (cls Ls).length, if (clAt Ls e).1 = i ∧ linkB g n Ls e (min a b) (max a b) = true then 1 else 0 := by
    intro b i
    rw [← card_filter, tst, length_filter_eq_card]
    congr 1
    ext e
    simp
  have h2 : ∀ b : ℕ, ∑ i ∈ range Ls.length, (tst g n Ls a b i).length ≤
      ∑ e ∈ range (cls Ls).length, if linkB g n Ls e (min a b) (max a b) = true then 1 else 0 := by
    intro b
    rw [sum_congr rfl fun i _ => h1 b i, sum_comm]
    refine sum_le_sum fun e _ => ?_
    split_ifs with hl
    · simp only [hl, and_true]
      rw [← card_filter]
      exact card_le_one.2 fun i hi j hj => (mem_filter.1 hi).2.symm.trans (mem_filter.1 hj).2
    · simp [hl]
  refine (sum_le_sum fun b _ => h2 b).trans ?_
  rw [sum_comm]
  refine (sum_le_sum fun e _ => ?_).trans (b := ∑ e ∈ range (cls Ls).length, if tchB g n Ls a e = true then 2 else 0) ?_
  · rw [← card_filter]
    exact card_links_at_le ha e
  · rw [← sum_filter, sum_const, smul_eq_mul, Nat.mul_comm, tch, length_filter_eq_card]


/-! ### The size of the network -/

/-- The sum of a list indexed by the numbers below R, as a sum over a finite set. -/
theorem sum_map_range (f : ℕ → ℕ) (R : ℕ) : ((List.range R).map f).sum = ∑ i ∈ range R, f i := by
  induction R with
  | zero => simp
  | succ R ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

/-- A string of t bits has at most t blocks. -/
theorem ceil_le {b : ℕ} (h0 : 0 < b) (t : ℕ) : (t + b - 1) / b ≤ t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rw [Nat.zero_add]; exact (Nat.div_eq_of_lt (by omega)).le
  · refine Nat.div_le_of_le_mul ?_
    obtain ⟨b', rfl⟩ := Nat.exists_eq_succ_of_ne_zero h0.ne'
    obtain ⟨t', rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
    have : (b' + 1) * (t' + 1) = b' * t' + b' + t' + 1 := by ring
    simp only [Nat.succ_eq_add_one]
    omega

/-- The number that a profile prescribes for two nodes does not depend on their order. -/
theorem mu_comm (y a b i : ℕ) : mu g Ls y a b i = mu g Ls y b a i := by simp only [mu, min_comm, max_comm]
/-- The clauses whose marks two nodes compare do not depend on the order of the nodes. -/
theorem tst_comm (a b i : ℕ) : tst g n Ls a b i = tst g n Ls b a i := by simp only [tst, min_comm, max_comm]
/-- The capacities are symmetric. -/
theorem mcap_comm (β b y a a' : ℕ) : mcap g n β b Ls y a a' = mcap g n β b Ls y a' a := by
  simp only [mcap, mu_comm y a a', tst_comm a a']

/-- `adm` is true exactly when, in every layer, the four conditions below hold. -/
theorem adm_iff {k w y : ℕ} : adm k g n w Ls y = true ↔ ∀ i < Ls.length,
    ((List.range g).map fun a => mu g Ls y a a i).sum ≤ w ∧
    ((List.range g).map fun a => ((List.range a).map fun a' => mu g Ls y a' a i).sum).sum ≤ (k - 1) * w ∧
    ∀ a < g, ∀ a' < g, (a' < a → Groundwork.Prog.digit (cls Ls).length y ((a * g + a') * Ls.length + i) = 0) ∧
      (a < a' → mu g Ls y a a' i ≤ (tst g n Ls a a' i).length) := by
  simp only [adm, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  refine forall₂_congr fun i _ => ?_
  rw [and_assoc]
  refine and_congr_right fun _ => and_congr_right fun _ => forall₂_congr fun a _ => forall₂_congr fun a' _ => ?_
  split_ifs with h
  · simp only [beq_iff_eq]
    exact ⟨fun h0 => ⟨fun _ => h0, fun h' => absurd h (by omega)⟩, fun h0 => h0.1 h⟩
  · simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
    constructor
    · rintro (rfl | h0)
      · exact ⟨fun h' => absurd h' h, fun h' => absurd h' (lt_irrefl _)⟩
      · exact ⟨fun h' => absurd h' h, fun _ => h0⟩
    · intro h0
      rcases Nat.lt_or_ge a a' with hlt | hge
      · exact Or.inr (h0.2 hlt)
      · exact Or.inl (by omega)

/-- An admissible profile prescribes for two different nodes at most as many set marks as they
compare. -/
theorem mu_le_of_adm {k w y : ℕ} (h : adm k g n w Ls y = true) {a a' i : ℕ} (ha : a < g) (ha' : a' < g) (hne : a ≠ a') (hi : i < Ls.length) :
    mu g Ls y a a' i ≤ (tst g n Ls a a' i).length := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact ((adm_iff.1 h i hi).2.2 a ha a' ha').2 hlt
  · rw [mu_comm, tst_comm]; exact ((adm_iff.1 h i hi).2.2 a' ha' a ha).2 hgt

/-- The capacity of a pair is at most (2 + β) bits for each bit of its strings. -/
theorem mcap_le {k w y β b : ℕ} (h0 : 0 < b) (h : adm k g n w Ls y = true) {a a' : ℕ} (ha : a < g) (ha' : a' < g) (hne : a ≠ a') :
    mcap g n β b Ls y a a' ≤ (2 + β) * ∑ i ∈ range Ls.length, (tst g n Ls a a' i).length := by
  rw [mcap, sum_map_range, mul_sum]
  refine sum_le_sum fun i hi => ?_
  have h1 := mu_le_of_adm h ha ha' hne (mem_range.1 hi)
  have h2 := ceil_le h0 (tst g n Ls a a' i).length
  calc mu g Ls y a a' i * (1 + β) + ((tst g n Ls a a' i).length + b - 1) / b
      ≤ (tst g n Ls a a' i).length * (1 + β) + (tst g n Ls a a' i).length := Nat.add_le_add (Nat.mul_le_mul_right _ h1) h2
    _ = (2 + β) * (tst g n Ls a a' i).length := by ring

/-- The capacities at a node a sum to at most 2(2 + β) bits for each clause that touches a. -/
theorem sum_mcap_le {k w y β b : ℕ} (h0 : 0 < b) (h : adm k g n w Ls y = true) {a : ℕ} (ha : a < g) :
    ∑ a' ∈ (range g).erase a, mcap g n β b Ls y a a' ≤ 2 * (2 + β) * (tch g n Ls a).length := by
  calc ∑ a' ∈ (range g).erase a, mcap g n β b Ls y a a'
      ≤ ∑ a' ∈ (range g).erase a, (2 + β) * ∑ i ∈ range Ls.length, (tst g n Ls a a' i).length :=
        sum_le_sum fun a' ha' => mcap_le h0 h ha (mem_range.1 (mem_erase.1 ha').2) (mem_erase.1 ha').1.symm
    _ = (2 + β) * ∑ a' ∈ (range g).erase a, ∑ i ∈ range Ls.length, (tst g n Ls a a' i).length := by rw [mul_sum]
    _ ≤ (2 + β) * (2 * (tch g n Ls a).length) := Nat.mul_le_mul_left _ (sum_length_tst_node_le ha)
    _ = 2 * (2 + β) * (tch g n Ls a).length := by ring

/-- A sum over the other nodes, as a sum over numbers. -/
theorem sum_erase_fin (a : Fin g) (F : ℕ → ℕ) : ∑ b ∈ (univ : Finset (Fin g)).erase a, F b.val = ∑ b ∈ (range g).erase a.val, F b := by
  refine sum_bij (fun b _ => b.val) ?_ ?_ ?_ ?_
  · intro b hb
    exact mem_erase.2 ⟨fun h => (mem_erase.1 hb).1 (Fin.ext h), mem_range.2 b.2⟩
  · intro b _ b' _ h; exact Fin.ext h
  · intro b hb
    exact ⟨⟨b, mem_range.1 (mem_erase.1 hb).2⟩, mem_erase.2 ⟨fun h => (mem_erase.1 hb).1 (congrArg Fin.val h), mem_univ _⟩, rfl⟩
  · intro b _; rfl

/-- A number that is 0 or 1 is at most 1 in absolute value. -/
theorem abs_boole_le (p : Prop) [Decidable p] : |if p then (1 : ℤ) else 0| ≤ 1 := by
  split_ifs <;> simp

/-- The network of an admissible profile has size P, with entries 0, 1, −1, if at every node P
bounds qv plus the number of touching clauses, and
2(2 + β) times that number. -/
theorem sized_markN {gu nu βu bu : U} {k w y P : ℕ} (h0 : 0 < bu.length) (h : adm k gu.length nu.length w Ls y = true)
    (hP : ∀ a < gu.length, qv gu.length nu.length + (tch gu.length nu.length Ls a).length ≤ P ∧
      2 * (2 + βu.length) * (tch gu.length nu.length Ls a).length ≤ P) :
    (markN gu.length ((gu, nu, βu, bu), (Ls, y))).Sized P 0 where
  card_S a := by
    simp only [markN, markF, card_words]
    exact Nat.pow_le_pow_right (by norm_num) (hP a a.2).1
  c_symm a b := by simp only [markN, markF]; exact mcap_comm _ _ _ _ _
  sum_c a := by
    simp only [markN, markF]
    rw [sum_erase_fin a fun b' => mcap gu.length nu.length βu.length bu.length Ls y a.val b']
    exact (sum_mcap_le h0 h a.2).trans (hP a a.2).2
  card_lab a b _ := by
    simp only [Network.lab, markN, markF, card_words]
    refine Nat.pow_le_pow_right (by norm_num) (le_of_eq ?_)
    rcases le_total a b with hab | hab
    · rw [min_eq_left hab, max_eq_right hab]
    · rw [min_eq_right hab, max_eq_left hab, mcap_comm]
  abs_W a z := by
    simp only [markN, markF, mW, pow_zero]
    split_ifs
    · simp
    · simp
  abs_f a b z θ := by
    simp only [markN, markF, pow_zero]
    exact abs_boole_le _
  abs_Ψ a b z z' _ := by
    simp only [Network.Ψ, markN, markF, pow_zero]
    have e : ∀ (L L' θ : List Bool), ((if (L == θ) = true then (1 : ℤ) else 0) * if (L' == θ) = true then 1 else 0) =
        if θ = L ∧ θ = L' then 1 else 0 := by
      intro L L' θ
      by_cases h1 : θ = L
      · by_cases h2 : θ = L'
        · subst h1; simp [← h2]
        · have h2' : ¬ L' = θ := fun h => h2 h.symm
          simp [h2, h2']
      · have h1' : ¬ L = θ := fun h => h1 h.symm
        simp [h1, h1']
    simp only [e]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, abs_of_nonneg (Nat.cast_nonneg _)]
    refine Nat.cast_le_one.2 (card_le_one.2 fun θ hθ θ' hθ' => ?_)
    exact ((mem_filter.1 hθ).2.1).trans ((mem_filter.1 hθ').2.1).symm


/-! ### The shared bits -/

/-- A symmetric table summed over the ordered pairs of different numbers below g is twice its sum
over the pairs a' < a. -/
theorem sum_erase_eq_two_mul (F : ℕ → ℕ → ℕ) (hF : ∀ a b, F a b = F b a) (g : ℕ) :
    ∑ a ∈ range g, ∑ b ∈ (range g).erase a, F a b = 2 * ∑ a ∈ range g, ∑ a' ∈ range a, F a' a := by
  induction g with
  | zero => simp
  | succ g ih =>
    rw [sum_range_succ, sum_range_succ, Nat.mul_add, ← ih]
    have h1 : (range (g + 1)).erase g = range g := by
      rw [range_add_one, erase_insert notMem_range_self]
    have h2 : ∀ a ∈ range g, ∑ b ∈ (range (g + 1)).erase a, F a b = ∑ b ∈ (range g).erase a, F a b + F a g := by
      intro a ha
      have hne : g ≠ a := (mem_range.1 ha).ne'
      rw [range_add_one, erase_insert_of_ne hne, sum_insert (fun h => notMem_range_self (mem_erase.1 h).2), Nat.add_comm]
    rw [h1, sum_congr rfl h2, sum_add_distrib, sum_congr rfl fun b _ => hF g b]
    ring

/-- A string of t bits has at most t / b + 1 blocks. -/
theorem ceil_le_succ (b t : ℕ) : (t + b - 1) / b ≤ t / b + 1 := by
  rcases Nat.eq_zero_or_pos b with rfl | h0
  · simp
  · calc (t + b - 1) / b ≤ (t + b) / b := Nat.div_le_div_right (Nat.sub_le _ _)
      _ = t / b + 1 := Nat.add_div_right t h0

/-- Rounding down term by term gives at most the rounded-down quotient of the sum. -/
theorem sum_div_le {ι : Type} (s : Finset ι) (f : ι → ℕ) (b : ℕ) : ∑ i ∈ s, f i / b ≤ (∑ i ∈ s, f i) / b := by
  rcases Nat.eq_zero_or_pos b with rfl | h0
  · simp
  · rw [Nat.le_div_iff_mul_le h0, sum_mul]
    exact sum_le_sum fun i _ => Nat.div_mul_le_self _ _

/-- The sum over a' < a < g as a sum over all pairs. -/
theorem sum_lt_eq_sum_product (F : ℕ → ℕ → ℕ) (g : ℕ) :
    ∑ a ∈ range g, ∑ a' ∈ range a, F a' a = ∑ p ∈ (range g) ×ˢ (range g), if p.1 < p.2 then F p.1 p.2 else 0 := by
  rw [sum_product_right]
  refine sum_congr rfl fun a ha => ?_
  rw [← sum_filter]
  refine sum_congr ?_ fun _ _ => rfl
  ext a'
  simp only [mem_range, mem_filter]
  exact ⟨fun h => ⟨h.trans (mem_range.1 ha), h⟩, fun h => h.2⟩

/-- A bound on the shared bits of the network of an admissible profile whose clauses have at most k
literals. -/
theorem U_markN_le {gu nu βu bu : U} {w y k : ℕ} (h : adm k gu.length nu.length w Ls y = true) (hk : ∀ L ∈ Ls, ∀ C ∈ L, C.length ≤ k) :
    (markN gu.length ((gu, nu, βu, bu), (Ls, y))).U ≤
      2 * ∑ i ∈ range Ls.length, ((k - 1) * w * (1 + βu.length) + ((k - 1) * (Ls.getD i []).length / bu.length + gu.length * gu.length)) := by
  obtain ⟨g, hg⟩ : ∃ g, g = gu.length := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n, n = nu.length := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β, β = βu.length := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = bu.length := ⟨_, rfl⟩
  have hU : (markN gu.length ((gu, nu, βu, bu), (Ls, y))).U = ∑ a ∈ range g, ∑ a' ∈ (range g).erase a, mcap g n β b Ls y a a' := by
    subst hg hn hβ hb
    simp only [Network.U, markN, markF]
    rw [← Fin.sum_univ_eq_sum_range fun a => ∑ a' ∈ (range gu.length).erase a, mcap gu.length nu.length βu.length bu.length Ls y a a']
    exact sum_congr rfl fun a _ => sum_erase_fin a fun a' => mcap gu.length nu.length βu.length bu.length Ls y a.val a'
  rw [← hg, ← hn] at h
  rw [hU, ← hg, ← hβ, ← hb, sum_erase_eq_two_mul _ (mcap_comm β b y)]
  refine Nat.mul_le_mul_left 2 ?_
  simp only [mcap, sum_map_range]
  rw [sum_congr rfl fun a _ => sum_comm, sum_comm]
  refine sum_le_sum fun i hi => ?_
  simp only [sum_add_distrib]
  have hi' := mem_range.1 hi
  refine Nat.add_le_add ?_ ?_
  · have h2 := (adm_iff.1 h i hi').2.1
    simp only [sum_map_range] at h2
    simp only [← sum_mul]
    exact Nat.mul_le_mul_right _ h2
  · calc ∑ a ∈ range g, ∑ a' ∈ range a, ((tst g n Ls a' a i).length + b - 1) / b
        ≤ ∑ a ∈ range g, ∑ a' ∈ range a, ((tst g n Ls a' a i).length / b + 1) :=
          sum_le_sum fun a _ => sum_le_sum fun a' _ => ceil_le_succ b _
      _ = ∑ a ∈ range g, ∑ a' ∈ range a, (tst g n Ls a' a i).length / b + ∑ a ∈ range g, a := by
          simp only [sum_add_distrib, sum_const, card_range, smul_eq_mul, mul_one]
      _ ≤ (k - 1) * (Ls.getD i []).length / b + g * g := by
          refine Nat.add_le_add ?_ ?_
          · refine ((sum_le_sum fun a _ => sum_div_le _ _ b).trans (sum_div_le _ _ b)).trans (Nat.div_le_div_right ?_)
            rw [sum_lt_eq_sum_product fun a' a => (tst g n Ls a' a i).length]
            refine sum_length_tst_le k i fun C hC => hk _ ?_ C hC
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
            exact List.getElem_mem _
          · calc ∑ a ∈ range g, a ≤ ∑ _a ∈ range g, g := sum_le_sum fun a ha => (mem_range.1 ha).le
              _ = g * g := by simp


end PaddedDescent.F.Mark.Size

namespace PaddedDescent.F

open Mark Mark.Size Finset

/-- The network of an admissible profile of well-formed layers, each variable in at most Δ clauses,
has size `Pb`, entries 0, 1, −1, and at most `Ub` shared bits. -/
public theorem stMarkSized : StMarkSized := fun k gu nu βu bu w Δ Ls y hg h0 _ hwf hΔ hM hadm => by
  have htch := Deg.length_tch_le_of_wfL hg hwf hΔ
  refine ⟨sized_markN h0 hadm fun a _ => ?_, ?_⟩
  · have h1 := htch a
    have h2 : qv gu.length nu.length * Δ ≤ qv gu.length nu.length * (Δ + 4) := Nat.mul_le_mul_left _ (by omega)
    constructor
    · calc qv gu.length nu.length + (tch gu.length nu.length Ls a).length
          ≤ qv gu.length nu.length + qv gu.length nu.length * Δ := Nat.add_le_add_left h1 _
        _ ≤ 1 * (qv gu.length nu.length * (Δ + 4)) := by rw [Nat.one_mul, Nat.mul_add]; omega
        _ ≤ 2 * (2 + βu.length) * (qv gu.length nu.length * (Δ + 4)) := Nat.mul_le_mul_right _ (by omega)
        _ = Pb gu.length nu.length βu.length Δ := by rw [Pb]; ring
    · calc 2 * (2 + βu.length) * (tch gu.length nu.length Ls a).length
          ≤ 2 * (2 + βu.length) * (qv gu.length nu.length * (Δ + 4)) := Nat.mul_le_mul_left _ (h1.trans h2)
        _ = Pb gu.length nu.length βu.length Δ := by rw [Pb]; ring
  · refine (U_markN_le hadm fun L hL C hC => (hwf L hL C hC).2.1).trans ?_
    have hterm : ∀ i ∈ range Ls.length, (k - 1) * w * (1 + βu.length) + ((k - 1) * (Ls.getD i []).length / bu.length + gu.length * gu.length) ≤
        (k - 1) * w * (1 + βu.length) + (k - 1) * (nu.length + 1) + gu.length ^ 2 := by
      intro i hi
      have hi' := mem_range.1 hi
      have hlen : (Ls.getD i []).length ≤ Ls.flatten.length := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi', Option.getD_some]
        exact (List.sublist_flatten_of_mem (List.getElem_mem hi')).length_le
      have hdiv : (k - 1) * (Ls.getD i []).length / bu.length ≤ (k - 1) * (nu.length + 1) := by
        refine Nat.div_le_of_le_mul ?_
        calc (k - 1) * (Ls.getD i []).length ≤ (k - 1) * (bu.length * (nu.length + 1)) := Nat.mul_le_mul_left (k - 1) (hlen.trans hM)
          _ = bu.length * ((k - 1) * (nu.length + 1)) := by ring
      rw [sq]
      omega
    calc 2 * ∑ i ∈ range Ls.length, ((k - 1) * w * (1 + βu.length) + ((k - 1) * (Ls.getD i []).length / bu.length + gu.length * gu.length))
        ≤ 2 * ∑ _i ∈ range Ls.length, ((k - 1) * w * (1 + βu.length) + (k - 1) * (nu.length + 1) + gu.length ^ 2) :=
          Nat.mul_le_mul_left 2 (sum_le_sum hterm)
      _ = Ub k gu.length nu.length w βu.length Ls.length := by rw [sum_const, card_range, smul_eq_mul, Ub]; ring

end PaddedDescent.F
