/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.Interfaces
public import StepMachines.Math.Digits
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-! # Marks and layers: every set of clauses has exactly one profile

Here `Ls` is a list of formulas, the layers; their clauses are numbered together (`cls`), and the
layer of a clause is the index of its formula. A set P of clause indices
determines, for every layer, how many of its members each node owns and how many lie among the
clauses whose marks two nodes compare. These numbers are the digits of exactly one
number y below `nProf` whose unused places are 0 (`sum_digit_eq`, `adm_match_iff`). That y is
admissible exactly if every layer has at most w members of P: a clause has one owner,
so the owned members add up to the members of the layer (`sum_oc`); a clause of at most k literals
touches at most k nodes and has at most k − 1 links, so the compared members add up
to at most k − 1 times that number (`sum_pw_le`). The result is `stProfSum`, the interface statement
`StProfSum`. No state of the network occurs in this file. -/

public section

namespace PaddedDescent.F.Mark.Prof

open Groundwork Groundwork.Prog Groundwork.Grid Finset

/-! ### Digits -/

/-- Exactly one number below (M+1)^Q has prescribed digits t q ≤ M at the places q < Q, and none if
some t q exceeds M. -/
theorem sum_digit_eq (M Q : ℕ) (t : ℕ → ℕ) :
    ∑ y ∈ range ((M + 1) ^ Q), (if ∀ q < Q, digit M y q = t q then (1 : ℤ) else 0) = if ∀ q < Q, t q ≤ M then 1 else 0 := by
  classical
  have h := Prog.sum_digits M Q (fun φ => if φ = (fun q : Fin Q => t q) then (1 : ℤ) else 0)
  have e : ∀ y, (∀ q < Q, digit M y q = t q) ↔ (fun q : Fin Q => digit M y q) = fun q : Fin Q => t q := fun y =>
    ⟨fun h => funext fun q => h q q.2, fun h q hq => congrFun h ⟨q, hq⟩⟩
  simp only [e]
  rw [h, Finset.sum_ite_eq']
  refine if_congr ?_ rfl rfl
  rw [Fintype.mem_piFinset]
  exact ⟨fun h q hq => Nat.lt_succ_iff.1 (mem_range.1 (h ⟨q, hq⟩)), fun h q => mem_range.2 (Nat.lt_succ_iff.2 (h q q.2))⟩

/-- The place (A·g + A')·R + i determines i, A' and A. -/
theorem place_dec {g R A A' i : ℕ} (hA' : A' < g) (hi : i < R) :
    ((A * g + A') * R + i) % R = i ∧ ((A * g + A') * R + i) / R % g = A' ∧ ((A * g + A') * R + i) / R / g = A := by
  have hR : 0 < R := by omega
  have hg : 0 < g := by omega
  have h1 : ((A * g + A') * R + i) / R = A * g + A' := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hR, Nat.div_eq_of_lt hi, Nat.zero_add]
  have h2 : ((A * g + A') * R + i) % R = i := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  have h3 : (A * g + A') % g = A' := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hA']
  have h4 : (A * g + A') / g = A := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hg, Nat.div_eq_of_lt hA', Nat.zero_add]
  rw [h1]
  exact ⟨h2, h3, h4⟩

/-- A sum over `List.range` is the sum over `Finset.range`. -/
theorem sum_map_range (f : ℕ → ℕ) (k : ℕ) : ((List.range k).map f).sum = ∑ a ∈ range k, f a := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- The profile's number for two nodes does not depend on their order. -/
theorem mu_comm (g : ℕ) (Ls : List Fml) (y a b i : ℕ) : mu g Ls y a b i = mu g Ls y b a i := by
  unfold mu; rw [min_comm, max_comm]

/-- For a ≤ b the profile's number is the digit at the place (a·g + b)·R + i, where R is the number
of layers. -/
theorem mu_of_le (g : ℕ) (Ls : List Fml) (y : ℕ) {a b : ℕ} (h : a ≤ b) (i : ℕ) :
    mu g Ls y a b i = digit (cls Ls).length y ((a * g + b) * Ls.length + i) := by
  unfold mu; rw [min_eq_left h, max_eq_right h]

/-- The number of compared members does not depend on the order of the two nodes. -/
theorem pw_comm (g n : ℕ) (Ls : List Fml) (P : Finset ℕ) (a b i : ℕ) : pw g n Ls P a b i = pw g n Ls P b a i := by
  unfold pw tst; rw [min_comm, max_comm]

/-! ### Clauses, touched nodes, owners, links -/

/-- A clause of well-formed layers has 1 to k literals on variables below n. -/
theorem clAt_wf {k n : ℕ} {Ls : List Fml} (h : WfL k n Ls) {e : ℕ} (he : e < (cls Ls).length) :
    (clAt Ls e).2 ≠ [] ∧ (clAt Ls e).2.length ≤ k ∧ ∀ l ∈ (clAt Ls e).2, l.1 < n := by
  have hm : clAt Ls e ∈ cls Ls := by
    unfold clAt
    rw [List.getD_eq_getElem _ _ he]
    exact List.getElem_mem he
  unfold cls at hm
  rw [List.mem_flatMap] at hm
  obtain ⟨i, hi, hm⟩ := hm
  rw [List.mem_map] at hm
  obtain ⟨C, hC, hCe⟩ := hm
  rw [← hCe]
  have hi' := List.mem_range.1 hi
  have hL : Ls.getD i [] ∈ Ls := by
    rw [List.getD_eq_getElem _ _ hi']
    exact List.getElem_mem hi'
  exact h _ hL C hC

/-- The home of a variable below n is a node below g. -/
theorem home_lt {g n x : ℕ} (hg : 0 < g) (hx : x < n) : x / qv g n < g := by
  have h1 := Nat.lt_mul_div_succ (n + g - 1) hg
  have h2 : g * ((n + g - 1) / g + 1) = g * ((n + g - 1) / g) + g := by ring
  refine Nat.div_lt_of_lt_mul ?_
  unfold qv
  rw [Nat.mul_comm]
  omega

/-- The nodes below g that the clause e touches. -/
def tset (g n : ℕ) (Ls : List Fml) (e : ℕ) : Finset ℕ := (range g).filter fun a => tchB g n Ls a e = true

/-- Membership in `tset`. -/
theorem mem_tset {g n : ℕ} {Ls : List Fml} {e a : ℕ} : a ∈ tset g n Ls e ↔ a < g ∧ tchB g n Ls a e = true := by
  simp [tset]

/-- A clause touches some node below g. -/
theorem tset_nonempty {k g n : ℕ} {Ls : List Fml} (hg : 0 < g) (h : WfL k n Ls) {e : ℕ} (he : e < (cls Ls).length) :
    (tset g n Ls e).Nonempty := by
  obtain ⟨h1, _, h3⟩ := clAt_wf h he
  obtain ⟨l, hl⟩ := List.exists_mem_of_ne_nil _ h1
  refine ⟨l.1 / qv g n, mem_tset.2 ⟨home_lt hg (h3 l hl), ?_⟩⟩
  unfold tchB
  rw [List.any_eq_true]
  exact ⟨l, hl, by simp⟩

/-- A clause touches at most k nodes. -/
theorem card_tset_le {k g n : ℕ} {Ls : List Fml} (h : WfL k n Ls) {e : ℕ} (he : e < (cls Ls).length) :
    (tset g n Ls e).card ≤ k := by
  obtain ⟨_, h2, _⟩ := clAt_wf h he
  have hsub : tset g n Ls e ⊆ ((clAt Ls e).2.toFinset).image fun l => l.1 / qv g n := by
    intro a ha
    have h4 := (mem_tset.1 ha).2
    unfold tchB at h4
    rw [List.any_eq_true] at h4
    obtain ⟨l, hl, hla⟩ := h4
    exact mem_image.2 ⟨l, List.mem_toFinset.2 hl, by simpa using hla⟩
  calc (tset g n Ls e).card ≤ (((clAt Ls e).2.toFinset).image fun l => l.1 / qv g n).card := card_le_card hsub
    _ ≤ (clAt Ls e).2.toFinset.card := card_image_le
    _ ≤ (clAt Ls e).2.length := List.toFinset_card_le _
    _ ≤ k := h2

/-- What `ownB` says: a is touched, and no smaller node is. -/
theorem ownB_iff {g n : ℕ} {Ls : List Fml} {e a : ℕ} :
    ownB g n Ls e a = true ↔ tchB g n Ls a e = true ∧ ∀ c < g, c < a → tchB g n Ls c e = false := by
  unfold ownB
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]
  refine and_congr_right fun _ => forall₂_congr fun c _ => ?_
  tauto

/-- What `linkB` says: a < b are touched, and no node between them is. -/
theorem linkB_iff {g n : ℕ} {Ls : List Fml} {e a b : ℕ} :
    linkB g n Ls e a b = true ↔ a < b ∧ tchB g n Ls a e = true ∧ tchB g n Ls b e = true ∧
      ∀ c < g, a < c → c < b → tchB g n Ls c e = false := by
  unfold linkB
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨h1, h2, h3, fun c hc h5 h6 => by have := h4 c hc; tauto⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨⟨h1, h2⟩, h3⟩, fun c hc => by have := h4 c hc; tauto⟩

/-- Exactly one node below g owns a clause. -/
theorem card_owner {k g n : ℕ} {Ls : List Fml} (hg : 0 < g) (h : WfL k n Ls) {e : ℕ} (he : e < (cls Ls).length) :
    ((range g).filter fun a => ownB g n Ls e a = true).card = 1 := by
  have hne := tset_nonempty hg h he
  rw [card_eq_one]
  refine ⟨(tset g n Ls e).min' hne, ?_⟩
  ext a
  rw [mem_filter, mem_range, mem_singleton, ownB_iff]
  have h0 := mem_tset.1 (min'_mem _ hne)
  constructor
  · rintro ⟨ha, h1, h2⟩
    have h3 := min'_le _ a (mem_tset.2 ⟨ha, h1⟩)
    rcases Nat.lt_or_ge ((tset g n Ls e).min' hne) a with h4 | h4
    · have := h2 _ h0.1 h4
      rw [h0.2] at this
      exact absurd this (by simp)
    · omega
  · rintro rfl
    refine ⟨h0.1, h0.2, fun c hc hlt => ?_⟩
    by_contra hcon
    have hc' : tchB g n Ls c e = true := by simpa using hcon
    have := min'_le _ c (mem_tset.2 ⟨hc, hc'⟩)
    omega

/-- A clause has at most k − 1 links. -/
theorem card_links_le {k g n : ℕ} {Ls : List Fml} (hg : 0 < g) (h : WfL k n Ls) {e : ℕ} (he : e < (cls Ls).length) :
    ((range g ×ˢ range g).filter fun p => linkB g n Ls e p.1 p.2 = true).card ≤ k - 1 := by
  have hne := tset_nonempty hg h he
  have h0 := min'_mem _ hne
  have hcard : ((tset g n Ls e).erase ((tset g n Ls e).min' hne)).card ≤ k - 1 := by
    rw [card_erase_of_mem h0]
    have := card_tset_le (g := g) h he
    omega
  refine le_trans (card_le_card_of_injOn (fun p => p.2) ?_ ?_) hcard
  · intro p hp
    have hp' := mem_filter.1 (mem_coe.1 hp)
    obtain ⟨h1, h2, h3, _⟩ := linkB_iff.1 hp'.2
    have hp1 := mem_product.1 hp'.1
    refine mem_coe.2 (mem_erase.2 ⟨?_, mem_tset.2 ⟨mem_range.1 hp1.2, h3⟩⟩)
    intro heq
    have := min'_le _ p.1 (mem_tset.2 ⟨mem_range.1 hp1.1, h2⟩)
    simp only at heq
    omega
  · intro p hp p' hp' heq
    have hq := mem_filter.1 (mem_coe.1 hp)
    have hq' := mem_filter.1 (mem_coe.1 hp')
    obtain ⟨h1, h2, _, h4⟩ := linkB_iff.1 hq.2
    obtain ⟨h1', h2', _, h4'⟩ := linkB_iff.1 hq'.2
    have hr := mem_product.1 hq.1
    have hr' := mem_product.1 hq'.1
    simp only at heq
    have h5 : p.1 = p'.1 := by
      rcases Nat.lt_trichotomy p.1 p'.1 with hlt | heq' | hlt
      · have := h4 p'.1 (mem_range.1 hr'.1) hlt (by omega)
        rw [h2'] at this
        exact absurd this (by simp)
      · exact heq'
      · have := h4' p.1 (mem_range.1 hr.1) hlt (by omega)
        rw [h2] at this
        exact absurd this (by simp)
    exact Prod.ext h5 heq

/-! ### The two sums of a layer -/

/-- The owned members of a layer, summed over the nodes, are the members of the layer. -/
theorem sum_oc {k g n : ℕ} {Ls : List Fml} (hg : 0 < g) (h : WfL k n Ls) {P : Finset ℕ} (hP : P ⊆ range (cls Ls).length) (i : ℕ) :
    ∑ a ∈ range g, oc g n Ls P a i = (layP Ls P i).card := by
  have e1 : ∀ a, oc g n Ls P a i = ∑ e ∈ layP Ls P i, if ownB g n Ls e a = true then 1 else 0 := by
    intro a
    unfold oc layP
    rw [← card_filter, filter_filter]
  simp only [e1]
  rw [sum_comm]
  have e2 : ∀ e ∈ layP Ls P i, ∑ a ∈ range g, (if ownB g n Ls e a = true then 1 else 0) = 1 := by
    intro e he
    rw [← card_filter]
    exact card_owner hg h (mem_range.1 (hP (mem_filter.1 he).1))
  rw [sum_congr rfl e2]
  simp

/-- Membership in `tst` for a' < a. -/
theorem mem_tst {g n : ℕ} {Ls : List Fml} {a' a i e : ℕ} (hlt : a' < a) :
    e ∈ tst g n Ls a' a i ↔ e < (cls Ls).length ∧ (clAt Ls e).1 = i ∧ linkB g n Ls e a' a = true := by
  unfold tst
  rw [List.mem_filter, List.mem_range, min_eq_left hlt.le, max_eq_right hlt.le, Bool.and_eq_true, beq_iff_eq]

/-- The compared members of a layer, summed over the pairs of nodes, are at most k − 1 times the
members of the layer. -/
theorem sum_pw_le {k g n : ℕ} {Ls : List Fml} (hg : 0 < g) (h : WfL k n Ls) {P : Finset ℕ} (hP : P ⊆ range (cls Ls).length) (i : ℕ) :
    ∑ a ∈ range g, ∑ a' ∈ range a, pw g n Ls P a' a i ≤ (k - 1) * (layP Ls P i).card := by
  have e1 : ∀ a, ∀ a' ∈ range a, pw g n Ls P a' a i = ∑ e ∈ layP Ls P i, if linkB g n Ls e a' a = true then 1 else 0 := by
    intro a a' ha'
    unfold pw layP
    rw [← card_filter, filter_filter]
    congr 1
    refine filter_congr fun e he => ?_
    rw [mem_tst (mem_range.1 ha')]
    have := mem_range.1 (hP he)
    tauto
  calc ∑ a ∈ range g, ∑ a' ∈ range a, pw g n Ls P a' a i
      = ∑ a ∈ range g, ∑ a' ∈ range a, ∑ e ∈ layP Ls P i, (if linkB g n Ls e a' a = true then 1 else 0) :=
        sum_congr rfl fun a _ => sum_congr rfl fun a' ha' => e1 a a' ha'
    _ ≤ ∑ a ∈ range g, ∑ a' ∈ range g, ∑ e ∈ layP Ls P i, (if linkB g n Ls e a' a = true then 1 else 0) :=
        sum_le_sum fun a ha => sum_le_sum_of_subset (range_subset_range.2 (mem_range.1 ha).le)
    _ = ∑ e ∈ layP Ls P i, ∑ a' ∈ range g, ∑ a ∈ range g, (if linkB g n Ls e a' a = true then 1 else 0) := by
        rw [sum_comm]
        rw [sum_congr rfl fun a' _ => sum_comm]
        rw [sum_comm]
    _ = ∑ e ∈ layP Ls P i, ((range g ×ˢ range g).filter fun p => linkB g n Ls e p.1 p.2 = true).card := by
        refine sum_congr rfl fun e _ => ?_
        rw [card_filter, sum_product]
    _ ≤ ∑ _e ∈ layP Ls P i, (k - 1) := sum_le_sum fun e he => card_links_le hg h (mem_range.1 (hP (mem_filter.1 he).1))
    _ = (k - 1) * (layP Ls P i).card := by rw [sum_const, smul_eq_mul, Nat.mul_comm]

/-- At most as many members are compared as there are compared clauses. -/
theorem pw_le_length (g n : ℕ) (Ls : List Fml) (P : Finset ℕ) (a b i : ℕ) : pw g n Ls P a b i ≤ (tst g n Ls a b i).length := by
  unfold pw
  calc (P.filter fun e => e ∈ tst g n Ls a b i).card ≤ (tst g n Ls a b i).toFinset.card :=
        card_le_card fun e he => List.mem_toFinset.2 (mem_filter.1 he).2
    _ ≤ _ := List.toFinset_card_le _

/-! ### The profile of a set of clauses -/

/-- What `adm` says. -/
theorem adm_iff (k g n w : ℕ) (Ls : List Fml) (y : ℕ) : adm k g n w Ls y = true ↔ ∀ i < Ls.length,
    ∑ a ∈ range g, mu g Ls y a a i ≤ w ∧ ∑ a ∈ range g, ∑ a' ∈ range a, mu g Ls y a' a i ≤ (k - 1) * w ∧
    ∀ a < g, ∀ a' < g, (a' < a → digit (cls Ls).length y ((a * g + a') * Ls.length + i) = 0) ∧
      (a < a' → mu g Ls y a a' i ≤ (tst g n Ls a a' i).length) := by
  unfold adm
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq, sum_map_range]
  refine forall₂_congr fun i _ => ?_
  rw [and_assoc]
  refine and_congr_right fun _ => and_congr_right fun _ => forall₂_congr fun a _ => forall₂_congr fun a' _ => ?_
  by_cases h1 : a' < a
  · simp [h1, Nat.lt_asymm h1]
  · rcases Nat.eq_or_lt_of_le (Nat.le_of_not_lt h1) with h2 | h2
    · subst h2; simp
    · simp [h1, h2, Nat.ne_of_gt h2]

/-- The digit that the profile of P has at the place q. -/
def tgt (g n : ℕ) (Ls : List Fml) (P : Finset ℕ) (q : ℕ) : ℕ :=
  if q / Ls.length % g < q / Ls.length / g then 0
  else if q / Ls.length / g = q / Ls.length % g then oc g n Ls P (q / Ls.length / g) (q % Ls.length)
  else pw g n Ls P (q / Ls.length / g) (q / Ls.length % g) (q % Ls.length)

/-- The digit of P at the place (A·g + A')·R + i, where R is the number of layers. -/
theorem tgt_place {g n : ℕ} {Ls : List Fml} (P : Finset ℕ) {A A' i : ℕ} (hA' : A' < g) (hi : i < Ls.length) :
    tgt g n Ls P ((A * g + A') * Ls.length + i) =
      if A' < A then 0 else if A = A' then oc g n Ls P A i else pw g n Ls P A A' i := by
  obtain ⟨d1, d2, d3⟩ := place_dec (A := A) hA' hi
  unfold tgt
  rw [d1, d2, d3]

/-- The digits of P are at most the number of clauses. -/
theorem tgt_le {g n : ℕ} {Ls : List Fml} {P : Finset ℕ} (hP : P ⊆ range (cls Ls).length) (q : ℕ) :
    tgt g n Ls P q ≤ (cls Ls).length := by
  have hc : P.card ≤ (cls Ls).length := by simpa using card_le_card hP
  unfold tgt oc pw
  split_ifs
  · exact Nat.zero_le _
  · exact (card_filter_le _ _).trans hc
  · exact (card_filter_le _ _).trans hc

/-- y is an admissible profile of P exactly if the caps hold for P and y has the digits of P. -/
theorem adm_match_iff {k g n : ℕ} (w : ℕ) {Ls : List Fml} (hg : 0 < g) (h : WfL k n Ls) {P : Finset ℕ} (hP : P ⊆ range (cls Ls).length)
    (y : ℕ) : (adm k g n w Ls y = true ∧ Match g n Ls y P) ↔
      ((∀ i < Ls.length, (layP Ls P i).card ≤ w) ∧ ∀ q < g * g * Ls.length, digit (cls Ls).length y q = tgt g n Ls P q) := by
  rw [adm_iff]
  constructor
  · rintro ⟨hadm, hM⟩
    refine ⟨fun i hi => ?_, fun q hq => ?_⟩
    · rw [← sum_oc hg h hP i, sum_congr rfl fun a ha => (hM i hi a (mem_range.1 ha)).1]
      exact (hadm i hi).1
    · obtain ⟨x, hx, i, hi, rfl⟩ := mixed_surj hq
      obtain ⟨A, hA, A', hA', rfl⟩ := mixed_surj hx
      rw [tgt_place P hA' hi]
      split_ifs with c1 c2
      · exact ((hadm i hi).2.2 A hA A' hA').1 c1
      · subst c2
        rw [(hM i hi A hA).1, mu_of_le g Ls y le_rfl]
      · have hlt : A < A' := by omega
        rw [(hM i hi A hA).2 A' hA' (by omega), mu_of_le g Ls y hlt.le]
  · rintro ⟨hc, hD⟩
    have dig : ∀ A < g, ∀ A' < g, ∀ i < Ls.length, digit (cls Ls).length y ((A * g + A') * Ls.length + i) =
        if A' < A then 0 else if A = A' then oc g n Ls P A i else pw g n Ls P A A' i := fun A hA A' hA' i hi => by
      rw [hD _ (mixed_lt (mixed_lt hA hA') hi), tgt_place P hA' hi]
    have hM : Match g n Ls y P := by
      intro i hi a ha
      refine ⟨?_, fun b hb hne => ?_⟩
      · rw [mu_of_le g Ls y le_rfl, dig a ha a ha i hi]; simp
      · rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
        · rw [mu_comm, mu_of_le g Ls y hlt.le, dig b hb a ha i hi, if_neg (by omega), if_neg (by omega), pw_comm]
        · rw [mu_of_le g Ls y hlt.le, dig a ha b hb i hi, if_neg (by omega), if_neg (by omega)]
    refine ⟨fun i hi => ⟨?_, ?_, fun a ha a' ha' => ⟨fun hlt => ?_, fun hlt => ?_⟩⟩, hM⟩
    · rw [← sum_congr rfl fun a ha => (hM i hi a (mem_range.1 ha)).1, sum_oc hg h hP i]
      exact hc i hi
    · rw [← sum_congr rfl fun a ha => sum_congr rfl fun a' ha' =>
        (hM i hi a' ((mem_range.1 ha').trans (mem_range.1 ha))).2 a (mem_range.1 ha) (by have := mem_range.1 ha'; omega)]
      exact (sum_pw_le hg h hP i).trans (Nat.mul_le_mul_left (k - 1) (hc i hi))
    · rw [dig a ha a' ha' i hi, if_pos hlt]
    · rw [← (hM i hi a ha).2 a' ha' (by omega)]
      exact pw_le_length _ _ _ _ _ _ _

/-- `StProfSum`. -/
theorem stProfSum : StProfSum := by
  classical
  intro k g n w Ls P hg h hP
  have key := adm_match_iff w hg h hP
  by_cases hc : ∀ i < Ls.length, (layP Ls P i).card ≤ w
  · rw [if_pos hc]
    calc _ = ∑ y ∈ range (((cls Ls).length + 1) ^ (g * g * Ls.length)),
          (if ∀ q < g * g * Ls.length, digit (cls Ls).length y q = tgt g n Ls P q then (1 : ℤ) else 0) :=
          sum_congr rfl fun y _ => if_congr (by rw [key y]; exact and_iff_right hc) rfl rfl
      _ = _ := by rw [sum_digit_eq, if_pos fun q _ => tgt_le hP q]
  · rw [if_neg hc]
    exact sum_eq_zero fun y _ => if_neg (by rw [key y]; exact fun hh => hc hh.1)

end PaddedDescent.F.Mark.Prof
