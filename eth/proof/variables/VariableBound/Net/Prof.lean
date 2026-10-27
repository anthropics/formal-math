/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Net.Basic
import StepMachines.Math.Digits
import PaddedDescent.F.MarkProf
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-! # Step 3, «Profiles»: every set of marked objects has exactly one profile

A set P of (positions of) objects stands for a tuple (Π₀, …, Π_r). It determines, for each kind κ,
how many of its members each node owns (`oc`) and how many lie among the objects with the test {a,
b}
(`pw`). These numbers are the digits of exactly one number y below `nPr` whose unused places are 0
(`adm_match_iff`, with `Mark.Prof.sum_digit_eq` of proof/rates/PaddedDescent/F/MarkProf.lean).

The sentence of the text «Every nonzero term belongs to exactly one profile, which has Σ_a μ_(a,0) = |Π₀|,
Σ_a μ_(a,1) = Σ_j |Π_j|, μ_(a,b,κ) ≤ t_(a,b,κ) and Σ_({a,b}) μ_(a,b,κ) ≤ (k − 1 + κ)·Σ_a μ_(a,κ)» is
proved, with Σ_j |Π_j| read as the number of marked incidences,
in two forms: for the numbers of P (`sum_oc`, `pw_le_length`, `sum_pw_le`) and for a profile y to
which P belongs (`tot_of_match`, `mu_le_of_match`, `totP_le_of_match`). An object has one owner; an
object of kind κ touches at
most k + κ nodes and so has at most k − 1 + κ tests (`card_links_le`). So the profile of P is
admissible iff |Π₀| = n̄ + 1 (for F: ≤ n̄) and Σ_j |Π_j| ≤ M: this is `stProf`, the interface
statement `StProf`. The number of
profiles is `stNPr`. No setting of the network occurs in this file.

Twin of proof/rates/PaddedDescent/F/MarkProf.lean (layers of clauses in place of kinds of objects;
there every clause has at most k − 1 tests and every layer has the same cap). -/

public section

namespace VariableBound.Net.Prof

open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F Finset
open PaddedDescent.F.Mark (Cl qv vio WfL occ nProf)

/-! ### Digits -/

/-- The number that the profile prescribes for two nodes does not depend on their order: μ_(a,b,κ) =
μ_(b,a,κ). -/
theorem mu_comm (g : ℕ) (D : Dat) (y a b κ : ℕ) : mu g D y a b κ = mu g D y b a κ := by
  unfold mu; rw [min_comm, max_comm]

/-- For a ≤ b the number that the profile prescribes is the digit at the place (a·g + b)·2 + κ. -/
theorem mu_of_le (g : ℕ) (D : Dat) (y : ℕ) {a b : ℕ} (h : a ≤ b) (κ : ℕ) :
    mu g D y a b κ = digit (objs D).length y ((a * g + b) * 2 + κ) := by
  unfold mu; rw [min_eq_left h, max_eq_right h]

/-- The number of members of P with the test {a, b} does not depend on the order of a and b. -/
theorem pw_comm (g n : ℕ) (D : Dat) (P : Finset ℕ) (a b κ : ℕ) : pw g n D P a b κ = pw g n D P b a κ := by
  unfold pw tst; rw [min_comm, max_comm]

/-- `tot` is Σ_a μ_(a,κ), as a sum over a finite set. -/
theorem tot_eq (g : ℕ) (D : Dat) (y κ : ℕ) : tot g D y κ = ∑ a ∈ range g, mu g D y a a κ :=
  Mark.Prof.sum_map_range _ _

/-- `totP` is Σ_({a,b}) μ_(a,b,κ), as a sum over the pairs a < b < g. -/
theorem totP_eq (g : ℕ) (D : Dat) (y κ : ℕ) : totP g D y κ = ∑ b ∈ range g, ∑ a ∈ range b, mu g D y a b κ := by
  unfold totP
  rw [Mark.Prof.sum_map_range]
  exact sum_congr rfl fun b _ => Mark.Prof.sum_map_range _ _

/-! ### Touched nodes, owners, tests -/

/-- The nodes below g that the object o touches. -/
def tset (g n : ℕ) (D : Dat) (o : ℕ) : Finset ℕ := (range g).filter fun a => tchB g n D a o = true

/-- Membership in `tset`. -/
theorem mem_tset {g n : ℕ} {D : Dat} {o a : ℕ} : a ∈ tset g n D o ↔ a < g ∧ tchB g n D a o = true := by
  simp [tset]

/-- If 0 < g and the data are well formed, an object o (o below the number of objects) touches some
node below g. -/
theorem tset_nonempty {k g n : ℕ} {D : Dat} (hg : 0 < g) (h : WfD k n D) {o : ℕ} (ho : o < (objs D).length) :
    (tset g n D o).Nonempty := by
  obtain ⟨a, ha, ht⟩ := Basic.exists_tch hg h ho
  exact ⟨a, mem_tset.2 ⟨ha, ht⟩⟩

/-- If the data are well formed, an object o (o below the number of objects) of kind κ touches at
most k + κ nodes. -/
theorem card_tset_le {k g n : ℕ} {D : Dat} (h : WfD k n D) {o : ℕ} (ho : o < (objs D).length) :
    (tset g n D o).card ≤ k + (obAt D o).1 :=
  (Basic.card_touched_le o).trans (Nat.add_le_add_right (Basic.clOf_wf h ho).2.1 _)

/-- What `ownB` says: a is touched, and no smaller node is. -/
theorem ownB_iff {g n : ℕ} {D : Dat} {o a : ℕ} :
    ownB g n D o a = true ↔ tchB g n D a o = true ∧ ∀ c < g, c < a → tchB g n D c o = false := by
  unfold ownB
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]
  refine and_congr_right fun _ => forall₂_congr fun c _ => ?_
  tauto

/-- What `linkB` says: a < b are touched, and no node between them is. -/
theorem linkB_iff {g n : ℕ} {D : Dat} {o a b : ℕ} :
    linkB g n D o a b = true ↔ a < b ∧ tchB g n D a o = true ∧ tchB g n D b o = true ∧
      ∀ c < g, a < c → c < b → tchB g n D c o = false := by
  unfold linkB
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not,
    decide_eq_true_eq]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨h1, h2, h3, fun c hc h5 h6 => by have := h4 c hc; tauto⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨⟨h1, h2⟩, h3⟩, fun c hc => by have := h4 c hc; tauto⟩

/-- If 0 < g and the data are well formed, exactly one node below g owns an object o (o below the
number of objects). -/
theorem card_owner {k g n : ℕ} {D : Dat} (hg : 0 < g) (h : WfD k n D) {o : ℕ} (ho : o < (objs D).length) :
    ((range g).filter fun a => ownB g n D o a = true).card = 1 := by
  have hne := tset_nonempty hg h ho
  rw [card_eq_one]
  refine ⟨(tset g n D o).min' hne, ?_⟩
  ext a
  rw [mem_filter, mem_range, mem_singleton, ownB_iff]
  have h0 := mem_tset.1 (min'_mem _ hne)
  constructor
  · rintro ⟨ha, h1, h2⟩
    have h3 := min'_le _ a (mem_tset.2 ⟨ha, h1⟩)
    rcases Nat.lt_or_ge ((tset g n D o).min' hne) a with h4 | h4
    · have := h2 _ h0.1 h4
      rw [h0.2] at this
      exact absurd this (by simp)
    · omega
  · rintro rfl
    refine ⟨h0.1, h0.2, fun c hc hlt => ?_⟩
    by_contra hcon
    have hc' : tchB g n D c o = true := by simpa using hcon
    have := min'_le _ c (mem_tset.2 ⟨hc, hc'⟩)
    omega

/-- Step 3: «an object of kind κ ∈ {0, 1} has at most k − 1 + κ tests», for an object o (o below the
number of objects), if 0 < g and the data are well formed. -/
theorem card_links_le {k g n : ℕ} {D : Dat} (hg : 0 < g) (h : WfD k n D) {o : ℕ} (ho : o < (objs D).length) :
    ((range g ×ˢ range g).filter fun p => linkB g n D o p.1 p.2 = true).card ≤ k - 1 + (obAt D o).1 := by
  have hne := tset_nonempty hg h ho
  have h0 := min'_mem _ hne
  have hcard : ((tset g n D o).erase ((tset g n D o).min' hne)).card ≤ k - 1 + (obAt D o).1 := by
    rw [card_erase_of_mem h0]
    have := card_tset_le (g := g) h ho
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

/-! ### The facts of the text, for the numbers of a set P of objects -/

/-- Step 3, «Profiles»: Σ_a μ_(a,κ) is the number of marked objects of kind κ, that is |Π₀| for κ =
0 and the number of marked incidences for κ = 1. Here for the numbers of P: the members of kind κ
that the nodes
own add up to the members of kind κ. Needs 0 < g, well-formed data, and that P is a set of positions
of objects. -/
theorem sum_oc {k g n : ℕ} {D : Dat} (hg : 0 < g) (h : WfD k n D) {P : Finset ℕ} (hP : P ⊆ range (objs D).length) (κ : ℕ) :
    ∑ a ∈ range g, oc g n D P a κ = (kP D P κ).card := by
  have e1 : ∀ a, oc g n D P a κ = ∑ o ∈ kP D P κ, if ownB g n D o a = true then 1 else 0 := by
    intro a
    unfold oc kP
    rw [← card_filter, filter_filter]
  simp only [e1]
  rw [sum_comm]
  have e2 : ∀ o ∈ kP D P κ, ∑ a ∈ range g, (if ownB g n D o a = true then 1 else 0) = 1 := by
    intro o ho
    rw [← card_filter]
    exact card_owner hg h (mem_range.1 (hP (mem_filter.1 ho).1))
  rw [sum_congr rfl e2]
  simp

/-- Membership in `tst` for a < b. -/
theorem mem_tst {g n : ℕ} {D : Dat} {a b κ o : ℕ} (hlt : a < b) :
    o ∈ tst g n D a b κ ↔ o < (objs D).length ∧ (obAt D o).1 = κ ∧ linkB g n D o a b = true := by
  unfold tst
  rw [List.mem_filter, List.mem_range, min_eq_left hlt.le, max_eq_right hlt.le, Bool.and_eq_true, beq_iff_eq]

/-- Step 3, «Profiles»: Σ_({a,b}) μ_(a,b,κ) ≤ (k − 1 + κ)·Σ_a μ_(a,κ). Here for the numbers of P:
the members of kind κ with the test {a, b}, summed over the pairs a < b < g, are at most k − 1 + κ
times the
members of kind κ. Needs 0 < g, well-formed data, and that P is a set of positions of objects. -/
theorem sum_pw_le {k g n : ℕ} {D : Dat} (hg : 0 < g) (h : WfD k n D) {P : Finset ℕ} (hP : P ⊆ range (objs D).length) (κ : ℕ) :
    ∑ b ∈ range g, ∑ a ∈ range b, pw g n D P a b κ ≤ (k - 1 + κ) * (kP D P κ).card := by
  have e1 : ∀ b, ∀ a ∈ range b, pw g n D P a b κ = ∑ o ∈ kP D P κ, if linkB g n D o a b = true then 1 else 0 := by
    intro b a ha
    unfold pw kP
    rw [← card_filter, filter_filter]
    congr 1
    refine filter_congr fun o ho => ?_
    rw [mem_tst (mem_range.1 ha)]
    have := mem_range.1 (hP ho)
    tauto
  calc ∑ b ∈ range g, ∑ a ∈ range b, pw g n D P a b κ
      = ∑ b ∈ range g, ∑ a ∈ range b, ∑ o ∈ kP D P κ, (if linkB g n D o a b = true then 1 else 0) :=
        sum_congr rfl fun b _ => sum_congr rfl fun a ha => e1 b a ha
    _ ≤ ∑ b ∈ range g, ∑ a ∈ range g, ∑ o ∈ kP D P κ, (if linkB g n D o a b = true then 1 else 0) :=
        sum_le_sum fun b hb => sum_le_sum_of_subset (range_subset_range.2 (mem_range.1 hb).le)
    _ = ∑ o ∈ kP D P κ, ∑ a ∈ range g, ∑ b ∈ range g, (if linkB g n D o a b = true then 1 else 0) := by
        rw [sum_comm]
        rw [sum_congr rfl fun a _ => sum_comm]
        rw [sum_comm]
    _ = ∑ o ∈ kP D P κ, ((range g ×ˢ range g).filter fun p => linkB g n D o p.1 p.2 = true).card := by
        refine sum_congr rfl fun o _ => ?_
        rw [card_filter, sum_product]
    _ ≤ ∑ _o ∈ kP D P κ, (k - 1 + κ) := sum_le_sum fun o ho => by
        have := card_links_le hg h (mem_range.1 (hP (mem_filter.1 ho).1))
        rwa [(mem_filter.1 ho).2] at this
    _ = (k - 1 + κ) * (kP D P κ).card := by rw [sum_const, smul_eq_mul, Nat.mul_comm]

/-- Step 3, «Profiles»: μ_(a,b,κ) ≤ t_(a,b,κ). Here for the numbers of P: at most as many members of
P have the test {a, b} as there are objects of kind κ with this test. -/
theorem pw_le_length (g n : ℕ) (D : Dat) (P : Finset ℕ) (a b κ : ℕ) : pw g n D P a b κ ≤ (tst g n D a b κ).length := by
  unfold pw
  calc (P.filter fun o => o ∈ tst g n D a b κ).card ≤ (tst g n D a b κ).toFinset.card :=
        card_le_card fun o ho => List.mem_toFinset.2 (mem_filter.1 ho).2
    _ ≤ _ := List.toFinset_card_le _

/-! ### The facts of the text, for a profile to which P belongs -/

/-- Step 3, «Profiles»: the profile y of a term has Σ_a μ_(a,κ) equal to the number of members of P
of kind κ, that is |Π₀| for κ = 0 and the number of marked incidences for κ = 1. Needs 0 < g,
well-formed data, that P is a set of positions of objects,
κ < 2, and that P belongs to y. -/
theorem tot_of_match {k g n : ℕ} {D : Dat} (hg : 0 < g) (h : WfD k n D) {P : Finset ℕ} (hP : P ⊆ range (objs D).length) {y : ℕ}
    (hM : Match g n D y P) {κ : ℕ} (hκ : κ < 2) : tot g D y κ = (kP D P κ).card := by
  rw [tot_eq, ← sum_oc hg h hP κ]
  exact sum_congr rfl fun a ha => ((hM κ hκ a (mem_range.1 ha)).1).symm

/-- Step 3, «Profiles»: the profile y of a term has μ_(a,b,κ) ≤ t_(a,b,κ), for nodes a ≠ b below g
and κ < 2, if P belongs to y. -/
theorem mu_le_of_match {g n : ℕ} {D : Dat} {P : Finset ℕ} {y : ℕ} (hM : Match g n D y P) {κ : ℕ} (hκ : κ < 2) {a b : ℕ} (ha : a < g) (hb : b < g)
    (hne : b ≠ a) : mu g D y a b κ ≤ (tst g n D a b κ).length := by
  rw [← (hM κ hκ a ha).2 b hb hne]
  exact pw_le_length _ _ _ _ _ _ _

/-- Step 3, «Profiles»: the profile y of a term has Σ_({a,b}) μ_(a,b,κ) ≤ (k − 1 + κ)·Σ_a μ_(a,κ).
Needs 0 < g, well-formed data, that P is a set of positions of objects, κ < 2, and that P belongs to
y. -/
theorem totP_le_of_match {k g n : ℕ} {D : Dat} (hg : 0 < g) (h : WfD k n D) {P : Finset ℕ} (hP : P ⊆ range (objs D).length) {y : ℕ}
    (hM : Match g n D y P) {κ : ℕ} (hκ : κ < 2) : totP g D y κ ≤ (k - 1 + κ) * tot g D y κ := by
  rw [tot_of_match hg h hP hM hκ, totP_eq, ← sum_congr rfl fun b hb => sum_congr rfl fun a ha =>
    (hM κ hκ a ((mem_range.1 ha).trans (mem_range.1 hb))).2 b (mem_range.1 hb) (by have := mem_range.1 ha; omega)]
  exact sum_pw_le hg h hP κ

/-! ### The profile of a set of objects -/

/-- What `admD` says. -/
theorem adm_iff (k g n nb M : ℕ) (D : Dat) (fl : Bool) (y : ℕ) : admD k g n nb M D fl y = true ↔
    (if fl = true then tot g D y 0 ≤ nb else tot g D y 0 = nb + 1) ∧ tot g D y 1 ≤ M ∧ ∀ κ < 2,
      totP g D y κ ≤ (k - 1 + κ) * tot g D y κ ∧
      ∀ a < g, ∀ b < g, (b < a → digit (objs D).length y ((a * g + b) * 2 + κ) = 0) ∧
        (a < b → mu g D y a b κ ≤ (tst g n D a b κ).length) := by
  unfold admD
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  rw [and_assoc]
  refine and_congr ?_ (and_congr_right fun _ => forall₂_congr fun κ _ => and_congr_right fun _ =>
    forall₂_congr fun a _ => forall₂_congr fun b _ => ?_)
  · cases fl <;> simp
  · by_cases h1 : b < a
    · simp [h1, Nat.lt_asymm h1]
    · rcases Nat.eq_or_lt_of_le (Nat.le_of_not_lt h1) with h2 | h2
      · subst h2; simp
      · simp [h1, h2, Nat.ne_of_gt h2]

/-- The digit that the profile of P has at the place q. -/
def tgt (g n : ℕ) (D : Dat) (P : Finset ℕ) (q : ℕ) : ℕ :=
  if q / 2 % g < q / 2 / g then 0
  else if q / 2 / g = q / 2 % g then oc g n D P (q / 2 / g) (q % 2)
  else pw g n D P (q / 2 / g) (q / 2 % g) (q % 2)

/-- The digit of P at the place (a·g + b)·2 + κ, for b < g and κ < 2. -/
theorem tgt_place {g n : ℕ} {D : Dat} (P : Finset ℕ) {a b κ : ℕ} (hb : b < g) (hκ : κ < 2) :
    tgt g n D P ((a * g + b) * 2 + κ) = if b < a then 0 else if a = b then oc g n D P a κ else pw g n D P a b κ := by
  obtain ⟨d1, d2, d3⟩ := Mark.Prof.place_dec (A := a) hb hκ
  unfold tgt
  rw [d1, d2, d3]

/-- The digits of a set P of positions of objects are at most the number I + m of objects. -/
theorem tgt_le {g n : ℕ} {D : Dat} {P : Finset ℕ} (hP : P ⊆ range (objs D).length) (q : ℕ) :
    tgt g n D P q ≤ (objs D).length := by
  have hc : P.card ≤ (objs D).length := by simpa using card_le_card hP
  unfold tgt oc pw
  split_ifs
  · exact Nat.zero_le _
  · exact (card_filter_le _ _).trans hc
  · exact (card_filter_le _ _).trans hc

/-- If 0 < g, the data are well formed and P is a set of positions of objects: y is an admissible
profile to which P belongs iff |Π₀| = n̄ + 1 (for F: ≤ n̄), Σ_j |Π_j| ≤ M, and y has the digits of
P. -/
theorem adm_match_iff {k g n : ℕ} (nb M : ℕ) {D : Dat} (fl : Bool) (hg : 0 < g) (h : WfD k n D) {P : Finset ℕ} (hP : P ⊆ range (objs D).length)
    (y : ℕ) : (admD k g n nb M D fl y = true ∧ Match g n D y P) ↔
      (Lim nb M D fl P ∧ ∀ q < g * g * 2, digit (objs D).length y q = tgt g n D P q) := by
  rw [adm_iff]
  constructor
  · rintro ⟨hadm, hM⟩
    refine ⟨?_, fun q hq => ?_⟩
    · have h0 := hadm.1
      have h1 := hadm.2.1
      rw [tot_of_match hg h hP hM (by omega)] at h0 h1
      exact ⟨h0, h1⟩
    · obtain ⟨x, hx, κ, hκ, rfl⟩ := mixed_surj hq
      obtain ⟨a, ha, b, hb, rfl⟩ := mixed_surj hx
      rw [tgt_place P hb hκ]
      split_ifs with c1 c2
      · exact ((hadm.2.2 κ hκ).2 a ha b hb).1 c1
      · subst c2
        rw [(hM κ hκ a ha).1, mu_of_le g D y le_rfl]
      · have hlt : a < b := by omega
        rw [(hM κ hκ a ha).2 b hb (by omega), mu_of_le g D y hlt.le]
  · rintro ⟨hc, hD⟩
    have dig : ∀ a < g, ∀ b < g, ∀ κ < 2, digit (objs D).length y ((a * g + b) * 2 + κ) =
        if b < a then 0 else if a = b then oc g n D P a κ else pw g n D P a b κ := fun a ha b hb κ hκ => by
      rw [hD _ (mixed_lt (mixed_lt ha hb) hκ), tgt_place P hb hκ]
    have hM : Match g n D y P := by
      intro κ hκ a ha
      refine ⟨?_, fun b hb hne => ?_⟩
      · rw [mu_of_le g D y le_rfl, dig a ha a ha κ hκ]; simp
      · rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
        · rw [mu_comm, mu_of_le g D y hlt.le, dig b hb a ha κ hκ, if_neg (by omega), if_neg (by omega), pw_comm]
        · rw [mu_of_le g D y hlt.le, dig a ha b hb κ hκ, if_neg (by omega), if_neg (by omega)]
    refine ⟨⟨?_, ?_, fun κ hκ => ⟨totP_le_of_match hg h hP hM hκ, fun a ha b hb => ⟨fun hlt => ?_, fun hlt => ?_⟩⟩⟩, hM⟩
    · rw [tot_of_match hg h hP hM (by omega)]; exact hc.1
    · rw [tot_of_match hg h hP hM (by omega)]; exact hc.2
    · rw [dig a ha b hb κ hκ, if_pos hlt]
    · exact mu_le_of_match hM hκ ha hb (by omega)

/-- `StProf`. Step 3, «Profiles»: «every nonzero term belongs to exactly one profile», and that
profile is admissible iff |Π₀| = n̄ + 1 (for F: ≤ n̄) and Σ_j |Π_j| ≤ M. In Lean: for g > 0,
well-formed data (WfD) and a set P of places of objects, the number of admissible profiles y < `nPr`
to which P belongs is 1 if P is within these limits, and 0 otherwise. -/
theorem stProf : StProf := by
  classical
  intro k g n nb M D fl P hg h hP
  have key := adm_match_iff nb M fl hg h hP
  by_cases hc : Lim nb M D fl P
  · rw [if_pos hc]
    calc _ = ∑ y ∈ range (((objs D).length + 1) ^ (g * g * 2)),
          (if ∀ q < g * g * 2, digit (objs D).length y q = tgt g n D P q then (1 : ℤ) else 0) :=
          sum_congr rfl fun y _ => if_congr (by rw [key y]; exact and_iff_right hc) rfl rfl
      _ = _ := by rw [Mark.Prof.sum_digit_eq, if_pos fun q _ => tgt_le hP q]
  · rw [if_neg hc]
    exact sum_eq_zero fun y _ => if_neg (by rw [key y]; exact fun hh => hc hh.1)

/-! ### The number of profiles -/

/-- Step 3: «there are I ≤ r·s̄ incidences»: if every check has at most s clauses, there are at most
r·s + m objects. -/
theorem length_objs_le {D : Dat} {s : ℕ} (hs : ∀ L ∈ D.2, L.length ≤ s) : (objs D).length ≤ D.2.length * s + D.1.length := by
  have h1 : (D.2.map List.length).sum ≤ (D.2.map List.length).length • s :=
    List.sum_le_card_nsmul _ _ fun x hx => by
      obtain ⟨L, hL, rfl⟩ := List.mem_map.1 hx
      exact hs L hL
  rw [List.length_map, smul_eq_mul] at h1
  rw [Basic.length_objs]
  omega

/-- `StNPr`. Step 3, «Profiles»: «of which there are at most (I + m + 1)^(2(g² + g))»: the number
`nPr` of the numbers y that are tried as profiles, the admissible ones among them, is at most this;
and I + m ≤ r·s + m. Needs that every check has at most s clauses. -/
theorem stNPr : StNPr := by
  intro g D s hs
  refine ⟨length_objs_le hs, ?_⟩
  unfold nPr nProf
  refine Nat.pow_le_pow_right (Nat.succ_pos _) ?_
  have : g * g * 2 + 2 * g = 2 * (g ^ 2 + g) := by ring
  omega

end VariableBound.Net.Prof
