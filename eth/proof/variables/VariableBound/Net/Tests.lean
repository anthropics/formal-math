/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Net.Basic
public import VariableBound.Net.Rank
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin

/-! # Step 3: the tests of the objects

The nodes that an object touches form a chain a₁ < … < a_t, and its tests are the pairs of
neighbours. So an object of kind κ has at most k − 1 + κ tests (`card_links_le`,
`sum_length_tst_le`: T_κ is at most
k − 1 + κ times the number of objects of kind κ), and at most two tests at one node
(`card_links_at_le`, `sum_length_tst_node_le`). There are m objects of kind 0 and I = Σ_j |Λ_j| of
kind 1.
The total U of the network of a profile is twice the sum of the c_(a,b) over the pairs a < b
(`U_eq`). -/

public section

namespace VariableBound.Net.Tests

open Groundwork Groundwork.Prog Finset

variable {k g n : ℕ} {D : Dat}

/-! ### The tests of one object -/

/-- a and b are neighbours in the chain of the object e exactly when a < b, e touches both, and e
touches no node between them. -/
theorem linkB_iff {e a b : ℕ} : linkB g n D e a b = true ↔
    a < b ∧ tchB g n D a e = true ∧ tchB g n D b e = true ∧ ∀ c < g, a < c → c < b → tchB g n D c e = false := by
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
theorem link_left_unique {e a a' b : ℕ} (hb : b ≤ g) (h : linkB g n D e a b = true) (h' : linkB g n D e a' b = true) : a = a' := by
  obtain ⟨h1, h2, -, h4⟩ := linkB_iff.1 h
  obtain ⟨h1', h2', -, h4'⟩ := linkB_iff.1 h'
  rcases lt_trichotomy a a' with hlt | heq | hgt
  · have := h4 a' (by omega) hlt h1'; rw [h2'] at this; exact absurd this (by simp)
  · exact heq
  · have := h4' a (by omega) hgt h1; rw [h2] at this; exact absurd this (by simp)

/-- The lower end of a link determines its upper end. -/
theorem link_right_unique {e a b b' : ℕ} (hb : b < g) (hb' : b' < g) (h : linkB g n D e a b = true) (h' : linkB g n D e a b' = true) : b = b' := by
  obtain ⟨h1, -, h3, h4⟩ := linkB_iff.1 h
  obtain ⟨h1', -, h3', h4'⟩ := linkB_iff.1 h'
  rcases lt_trichotomy b b' with hlt | heq | hgt
  · have := h4' b hb h1 hlt; rw [h3] at this; exact absurd this (by simp)
  · exact heq
  · have := h4 b' hb' h1' hgt; rw [h3'] at this; exact absurd this (by simp)


/-- An object that touches a node has fewer links than touched nodes. -/
theorem card_links_lt (e : ℕ) (h : ∃ a < g, tchB g n D a e = true) :
    #(((range g) ×ˢ (range g)).filter fun p => linkB g n D e p.1 p.2 = true) < #((range g).filter fun a => tchB g n D a e = true) := by
  classical
  -- the least touched node is the upper end of no link
  obtain ⟨a₀, ha₀, hmin⟩ : ∃ a₀ ∈ (range g).filter (fun a => tchB g n D a e = true),
      ∀ a ∈ (range g).filter (fun a => tchB g n D a e = true), a₀ ≤ a := by
    obtain ⟨a, ha, ht⟩ := h
    exact exists_min_image _ id ⟨a, mem_filter.2 ⟨mem_range.2 ha, ht⟩⟩
  have hinj : Set.InjOn (fun p : ℕ × ℕ => p.2) (((range g) ×ˢ (range g)).filter fun p => linkB g n D e p.1 p.2 = true : Finset (ℕ × ℕ)) := by
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

/-- Step 3: «an object of kind κ has at most k − 1 + κ tests»; here with the number of literals of
its clause in place of k. -/
theorem card_links_le (e : ℕ) :
    #(((range g) ×ˢ (range g)).filter fun p => linkB g n D e p.1 p.2 = true) ≤ (clOf D e).length + (obAt D e).1 - 1 := by
  by_cases h : ∃ a < g, tchB g n D a e = true
  · have := card_links_lt e h
    have := Basic.card_touched_le (g := g) (n := n) (D := D) e
    omega
  · rw [card_eq_zero.2]
    · exact Nat.zero_le _
    · refine filter_eq_empty_iff.2 fun p hp hl => h ⟨p.1, mem_range.1 (mem_product.1 hp).1, (linkB_iff.1 hl).2.1⟩

/-! ### Sums over pairs of nodes -/

/-- The sum of a list indexed by the numbers below R, as a sum over a finite set. -/
theorem sum_map_range (f : ℕ → ℕ) (R : ℕ) : ((List.range R).map f).sum = ∑ i ∈ range R, f i := by
  induction R with
  | zero => simp
  | succ R ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

/-- A sum over the other nodes, as a sum over numbers. -/
theorem sum_erase_fin (a : Fin g) (F : ℕ → ℕ) : ∑ b ∈ (univ : Finset (Fin g)).erase a, F b.val = ∑ b ∈ (range g).erase a.val, F b := by
  refine sum_bij (fun b _ => b.val) ?_ ?_ ?_ ?_
  · intro b hb
    exact mem_erase.2 ⟨fun h => (mem_erase.1 hb).1 (Fin.ext h), mem_range.2 b.2⟩
  · intro b _ b' _ h; exact Fin.ext h
  · intro b hb
    exact ⟨⟨b, mem_range.1 (mem_erase.1 hb).2⟩, mem_erase.2 ⟨fun h => (mem_erase.1 hb).1 (congrArg Fin.val h), mem_univ _⟩, rfl⟩
  · intro b _; rfl

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

/-! ### The number of tests of all objects of a kind -/

/-- Step 3, «The total»: T_κ, the number of tests of the objects of kind κ, is at most k − 1 + κ
times the number of these objects, if Φ has clauses of at most k literals (`WfD`). Sum over all
pairs of numbers below g. -/
theorem sum_length_tst_le' (hW : WfD k n D) (κ : ℕ) :
    ∑ p ∈ (range g) ×ˢ (range g), (if p.1 < p.2 then (tst g n D p.1 p.2 κ).length else 0) ≤
      (k - 1 + κ) * #((range (objs D).length).filter fun o => (obAt D o).1 = κ) := by
  have h1 : ∀ p : ℕ × ℕ, (if p.1 < p.2 then (tst g n D p.1 p.2 κ).length else 0) =
      ∑ e ∈ range (objs D).length, if (obAt D e).1 = κ ∧ linkB g n D e p.1 p.2 = true then 1 else 0 := by
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
  have h2 : ∀ e ∈ range (objs D).length, (∑ p ∈ (range g) ×ˢ (range g), if (obAt D e).1 = κ ∧ linkB g n D e p.1 p.2 = true then 1 else 0) ≤
      if (obAt D e).1 = κ then k - 1 + κ else 0 := by
    intro e he
    split_ifs with hi
    · simp only [hi, true_and]
      rw [← card_filter]
      have h3 := card_links_le (g := g) (n := n) (D := D) e
      have h4 := (Basic.clOf_wf hW (mem_range.1 he)).2.1
      omega
    · simp [hi]
  refine (sum_le_sum h2).trans ?_
  rw [← sum_filter, sum_const, smul_eq_mul, Nat.mul_comm]

/-- Step 3, «The total»: T_κ = Σ_(a < b < g) t_(a,b,κ) is at most k − 1 + κ times the number of
objects of kind κ, if Φ has clauses of at most k literals (`WfD`). -/
theorem sum_length_tst_le (hW : WfD k n D) (κ : ℕ) :
    ∑ b ∈ range g, ∑ a ∈ range b, (tst g n D a b κ).length ≤ (k - 1 + κ) * #((range (objs D).length).filter fun o => (obAt D o).1 = κ) := by
  rw [sum_lt_eq_sum_product fun a b => (tst g n D a b κ).length]
  exact sum_length_tst_le' hW κ

/-- There are m objects of kind 0 (for well-formed data, `WfD`). -/
theorem card_kind_zero (hW : WfD k n D) : #((range (objs D).length).filter fun o => (obAt D o).1 = 0) = D.1.length := by
  have h : ((range (objs D).length).filter fun o => (obAt D o).1 = 0) = range D.1.length := by
    ext o
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      exact (Basic.kind_zero_iff hW h1).1 h2
    · intro h1
      have h2 : o < (objs D).length := by rw [Basic.length_objs]; omega
      exact ⟨h2, (Basic.kind_zero_iff hW h2).2 h1⟩
  rw [h, card_range]

/-- There are I = Σ_j |Λ_j| objects of kind 1 (for well-formed data, `WfD`). -/
theorem card_kind_one (hW : WfD k n D) : #((range (objs D).length).filter fun o => (obAt D o).1 = 1) = (D.2.map List.length).sum := by
  have h1 := card_filter_add_card_filter_not (s := range (objs D).length) fun o => (obAt D o).1 = 0
  have h2 : ((range (objs D).length).filter fun o => ¬ (obAt D o).1 = 0) = (range (objs D).length).filter fun o => (obAt D o).1 = 1 := by
    refine filter_congr fun o ho => ?_
    have := Basic.kind_cases (D := D) (mem_range.1 ho)
    omega
  rw [h2, card_kind_zero hW, card_range] at h1
  have h3 := Basic.length_objs (D := D)
  omega

/-! ### The tests at one node -/

/-- At a node a, an object has at most two links, and none if it does not touch a. -/
theorem card_links_at_le {a : ℕ} (ha : a < g) (e : ℕ) :
    #(((range g).erase a).filter fun b => linkB g n D e (min a b) (max a b) = true) ≤ if tchB g n D a e = true then 2 else 0 := by
  classical
  split_ifs with ht
  · have hsub : (((range g).erase a).filter fun b => linkB g n D e (min a b) (max a b) = true) ⊆
        ((range g).filter fun b => linkB g n D e b a = true) ∪ ((range g).filter fun b => linkB g n D e a b = true) := by
      intro b hb
      obtain ⟨hb1, hb2⟩ := mem_filter.1 hb
      obtain ⟨hne, hbg⟩ := mem_erase.1 hb1
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [min_eq_right hlt.le, max_eq_left hlt.le] at hb2
        exact mem_union_left _ (mem_filter.2 ⟨hbg, hb2⟩)
      · rw [min_eq_left hgt.le, max_eq_right hgt.le] at hb2
        exact mem_union_right _ (mem_filter.2 ⟨hbg, hb2⟩)
    have c1 : #((range g).filter fun b => linkB g n D e b a = true) ≤ 1 :=
      card_le_one.2 fun b hb b' hb' => link_left_unique ha.le (mem_filter.1 hb).2 (mem_filter.1 hb').2
    have c2 : #((range g).filter fun b => linkB g n D e a b = true) ≤ 1 :=
      card_le_one.2 fun b hb b' hb' => link_right_unique (mem_range.1 (mem_filter.1 hb).1) (mem_range.1 (mem_filter.1 hb').1)
        (mem_filter.1 hb).2 (mem_filter.1 hb').2
    exact (card_le_card hsub).trans ((card_union_le _ _).trans (by omega))
  · refine le_of_eq (card_eq_zero.2 (filter_eq_empty_iff.2 fun b _ hl => ht ?_))
    obtain ⟨-, h2, h3, -⟩ := linkB_iff.1 hl
    rcases le_total a b with h | h
    · rwa [min_eq_left h] at h2
    · rwa [max_eq_left h] at h3

/-- Step 3, «The parameters»: «an object has at most two tests at a». All the strings that a node a
< g shares with the other nodes together have at most twice as many bits as objects touch a. -/
theorem sum_length_tst_node_le {a : ℕ} (ha : a < g) :
    ∑ b ∈ (range g).erase a, ∑ κ ∈ range 2, (tst g n D a b κ).length ≤ 2 * (tch g n D a).length := by
  have h1 : ∀ b κ : ℕ, (tst g n D a b κ).length =
      ∑ e ∈ range (objs D).length, if (obAt D e).1 = κ ∧ linkB g n D e (min a b) (max a b) = true then 1 else 0 := by
    intro b κ
    rw [← card_filter, tst, length_filter_eq_card]
    congr 1
    ext e
    simp
  have h2 : ∀ b : ℕ, ∑ κ ∈ range 2, (tst g n D a b κ).length ≤
      ∑ e ∈ range (objs D).length, if linkB g n D e (min a b) (max a b) = true then 1 else 0 := by
    intro b
    rw [sum_congr rfl fun κ _ => h1 b κ, sum_comm]
    refine sum_le_sum fun e _ => ?_
    split_ifs with hl
    · simp only [hl, and_true]
      rw [← card_filter]
      exact card_le_one.2 fun i hi j hj => (mem_filter.1 hi).2.symm.trans (mem_filter.1 hj).2
    · simp [hl]
  refine (sum_le_sum fun b _ => h2 b).trans ?_
  rw [sum_comm]
  refine (sum_le_sum fun e _ => ?_).trans (b := ∑ e ∈ range (objs D).length, if tchB g n D a e = true then 2 else 0) ?_
  · rw [← card_filter]
    exact card_links_at_le ha e
  · rw [← sum_filter, sum_const, smul_eq_mul, Nat.mul_comm, tch, length_filter_eq_card]

/-! ### The total -/

/-- c_(a,b) = c_(b,a). -/
theorem capD_comm (y a b : ℕ) : capD g n D y a b = capD g n D y b a := by
  simp only [capD, Rank.tst_comm g n D a b, Rank.mu_comm g D y a b]

/-- c_(a,b) as a sum over the two kinds. -/
theorem capD_eq (y a b : ℕ) : capD g n D y a b = ∑ κ ∈ range 2, cw (tst g n D a b κ).length (mu g D y a b κ) := by
  rw [capD, sum_map_range]

/-- A number written in unary has that length. -/
theorem length_rep (n : ℕ) : (rep n).length = n := by simp [rep]

/-- Step 3, «The total»: U = 2·Σ_({a,b}) c_(a,b), for the network of the profile y. -/
theorem U_eq (y : ℕ) (fl : Bool) : (netDN g (ctx g n D y fl)).U = 2 * ∑ b ∈ range g, ∑ a ∈ range b, capD g n D y a b := by
  have hU : (netDN g (ctx g n D y fl)).U = ∑ a ∈ range g, ∑ b ∈ (range g).erase a, capD g n D y a b := by
    simp only [Network.U, netDN, netD, ctx, length_rep]
    rw [← Fin.sum_univ_eq_sum_range fun a => ∑ b ∈ (range g).erase a, capD g n D y a b]
    exact sum_congr rfl fun a _ => sum_erase_fin a fun b => capD g n D y a.val b
  rw [hU, sum_erase_eq_two_mul _ (capD_comm y)]

end VariableBound.Net.Tests
