/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Net.Defs
import VariableBound.Net.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.List.Nodup
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Step 3, «The parameters»: the size of the weights, and display (69)

`abs_WD_le`: «A marked incidence that touches a is owned by a or has a test at a, so a setting of an
admissible profile has at most (k + 1)M of them; as |σ_i| ≤ 2^i, condition (ii) holds with B = (k + 1)M +
1», for the
weights W_a. In the order of the text: `own_or_test` (owned by a or a test at a), `card_marked_le`
(at most μ_(a,1) + Σ_(b ≠ a) μ_(a,b,1) marked incidences), `sum_mu_le_totP` and `marked_le` (at most
(k + 1)M), `abs_sig_le`
(|σ_i| ≤ 2^i).
`stP`: display (69), gP ≤ 2(n + g)(1 + Δ(t̄ + 3)) + 2(10n + g)·s̄ + g. -/

namespace VariableBound.Net.SizeB

open Groundwork Groundwork.Prog Finset PaddedDescent.F VariableBound.Net.Basic
open PaddedDescent.F.Mark (Cl qv vio WfL occ)

variable {k g n : ℕ} {D : Dat} {y : ℕ}

/-! ### The lists of objects (the same lemmas are in proof/variables/VariableBound/Net/Val.lean) -/

/-- Membership in the list of the objects that touch a. -/
theorem mem_tch {a e : ℕ} : e ∈ tch g n D a ↔ e < (objs D).length ∧ tchB g n D a e = true := by
  simp [tch]

/-- No object occurs twice in the list of the objects that touch a. -/
theorem nodup_tch (a : ℕ) : (tch g n D a).Nodup := List.Nodup.filter _ List.nodup_range

/-- {a, b} with a < b is a test of e iff e touches a and b and no node between them. -/
theorem linkB_iff {e a b : ℕ} : linkB g n D e a b = true ↔
    a < b ∧ tchB g n D a e = true ∧ tchB g n D b e = true ∧ ∀ c < g, a < c → c < b → tchB g n D c e = false := by
  simp only [linkB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_false_iff_not]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    refine ⟨h1, h2, h3, fun c hc h5 h6 => ?_⟩
    rcases h4 c hc with (h | h) | h
    · exact absurd h5 h
    · exact absurd h6 h
    · exact h
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨⟨h1, h2⟩, h3⟩, fun c hc => ?_⟩
    by_cases h5 : a < c
    · by_cases h6 : c < b
      · exact Or.inr (h4 c hc h5 h6)
      · exact Or.inl (Or.inr h6)
    · exact Or.inl (Or.inl h5)

/-- a owns e iff e touches a and no smaller node. -/
theorem ownB_iff {e a : ℕ} : ownB g n D e a = true ↔ tchB g n D a e = true ∧ ∀ c < g, c < a → tchB g n D c e = false := by
  simp only [ownB, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun c hc h3 => ?_⟩
    rcases h2 c hc with h | h
    · exact absurd h3 h
    · exact h
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun c hc => ?_⟩
    by_cases h3 : c < a
    · exact Or.inr (h2 c hc h3)
    · exact Or.inl h3

/-- Membership in the list of the objects of kind i with the test {a, b}. -/
theorem mem_tst {a b i e : ℕ} : e ∈ tst g n D a b i ↔
    e < (objs D).length ∧ (obAt D e).1 = i ∧ linkB g n D e (min a b) (max a b) = true := by
  simp [tst]

/-- No object occurs twice in the list of the objects with the test {a, b}. -/
theorem nodup_tst (a b i : ℕ) : (tst g n D a b i).Nodup := List.Nodup.filter _ List.nodup_range

/-- The length of a filtered list without repetitions is the number of elements of the set that it
lists. -/
theorem length_filter_eq_card {l : List ℕ} (hl : l.Nodup) (p : ℕ → Bool) (S : Finset ℕ) (h : ∀ e, (e ∈ l ∧ p e = true) ↔ e ∈ S) :
    (l.filter p).length = S.card := by
  rw [← List.toFinset_card_of_nodup (hl.filter p)]
  congr 1
  ext e
  rw [List.mem_toFinset, List.mem_filter]
  exact h e

/-- The sum of a list indexed by 0, …, R − 1 as a sum over a finite set. -/
theorem sum_map_range (f : ℕ → ℕ) (R : ℕ) : ((List.range R).map f).sum = ∑ i ∈ range R, f i := by
  induction R with
  | zero => simp
  | succ R ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

/-! ### A marked incidence that touches a is owned by a or has a test at a -/

/-- Step 3, «The parameters»: an object that touches the node a is owned by a or has a test {c, a}
with a node c < a. -/
theorem own_or_test {a o : ℕ} (h : tchB g n D a o = true) : ownB g n D o a = true ∨ ∃ c < a, linkB g n D o c a = true := by
  by_cases hs : ((range a).filter fun c => tchB g n D c o = true).Nonempty
  · right
    have hm := max'_mem _ hs
    obtain ⟨h1, h2⟩ := mem_filter.1 hm
    refine ⟨_, mem_range.1 h1, linkB_iff.2 ⟨mem_range.1 h1, h2, h, fun c _ h3 h4 => ?_⟩⟩
    by_contra h5
    have h5' : tchB g n D c o = true := by simpa using h5
    have h6 := le_max' ((range a).filter fun c => tchB g n D c o = true) c (mem_filter.2 ⟨mem_range.2 h4, h5'⟩)
    omega
  · left
    refine ownB_iff.2 ⟨h, fun c _ h3 => ?_⟩
    by_contra h5
    exact hs ⟨c, mem_filter.2 ⟨mem_range.2 h3, by simpa using h5⟩⟩

/-- The marked incidences that touch a, in the setting z. -/
def mk (g n : ℕ) (D : Dat) (a : ℕ) (z : List Bool) : Finset ℕ :=
  (range (objs D).length).filter fun o => tchB g n D a o = true ∧ (obAt D o).1 = 1 ∧ mark g n D a z o = true

/-- What a setting of the profile y has: μ_(a,κ) marked objects of kind κ owned by a, and μ_(a,b,κ)
marked objects of kind κ with the test {a, b}. -/
theorem okD_spec {a : ℕ} {z : List Bool} (h : okD g n D y a z = true) :
    (∀ κ < 2, ((tch g n D a).filter fun o => (obAt D o).1 == κ && ownB g n D o a && mark g n D a z o).length = mu g D y a a κ) ∧
      ∀ b < g, b ≠ a → ∀ κ < 2, (str g n D a b κ z).count true = mu g D y a b κ := by
  simp only [okD, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq, Bool.or_eq_true] at h
  obtain ⟨⟨_, h3⟩, h4⟩ := h
  exact ⟨h3, fun b hb hne κ hκ => (h4 b hb).resolve_left hne κ hκ⟩

/-- Step 3, «The parameters»: a setting z of the node a < g in the network of the profile y has at
most μ_(a,1) + Σ_(b ≠ a) μ_(a,b,1) marked incidences. -/
theorem card_marked_le {a : ℕ} {z : List Bool} (ha : a < g) (h : okD g n D y a z = true) :
    #(mk g n D a z) ≤ mu g D y a a 1 + ∑ b ∈ (range g).erase a, mu g D y a b 1 := by
  obtain ⟨h1, h2⟩ := okD_spec h
  have hO : mu g D y a a 1 = #((range (objs D).length).filter fun o => tchB g n D a o = true ∧ (obAt D o).1 = 1 ∧ ownB g n D o a = true ∧ mark g n D a z o = true) := by
    rw [← h1 1 (by norm_num)]
    refine length_filter_eq_card (nodup_tch a) _ _ fun e => ?_
    simp only [mem_tch, Bool.and_eq_true, beq_iff_eq, mem_filter, mem_range]
    tauto
  have hT : ∀ b ∈ (range g).erase a, mu g D y a b 1 = #((range (objs D).length).filter fun o => o ∈ tst g n D a b 1 ∧ mark g n D a z o = true) := by
    intro b hb
    obtain ⟨hne, hb⟩ := mem_erase.1 hb
    rw [← h2 b (mem_range.1 hb) hne 1 (by norm_num), str, List.count, List.countP_map, List.countP_eq_length_filter]
    refine length_filter_eq_card (nodup_tst a b 1) _ _ fun e => ?_
    simp only [Function.comp, beq_iff_eq, mem_filter, mem_range]
    exact ⟨fun hh => ⟨(mem_tst.1 hh.1).1, hh⟩, fun hh => hh.2⟩
  rw [hO, sum_congr rfl hT]
  refine le_trans (card_le_card ?_) ((card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))
  intro o ho
  obtain ⟨h3, h4, h5, h6⟩ := mem_filter.1 ho
  rcases own_or_test h4 with h7 | ⟨c, hc, h7⟩
  · exact mem_union_left _ (mem_filter.2 ⟨h3, h4, h5, h7, h6⟩)
  · refine mem_union_right _ (mem_biUnion.2 ⟨c, mem_erase.2 ⟨hc.ne, mem_range.2 (hc.trans ha)⟩, mem_filter.2 ⟨h3, mem_tst.2 ⟨mem_range.1 h3, h5, ?_⟩, h6⟩⟩)
    rwa [min_eq_right hc.le, max_eq_left hc.le]

/-- The numbers μ_(a,b,κ) of the pairs {a, b} with one fixed node a < g add up to at most μ_κ, the
sum over all pairs. -/
theorem sum_mu_le_totP {a : ℕ} (ha : a < g) (κ : ℕ) : ∑ b ∈ (range g).erase a, mu g D y a b κ ≤ totP g D y κ := by
  have e : totP g D y κ = ∑ p ∈ (range g).sigma fun b => range b, mu g D y p.2 p.1 κ := by
    rw [totP, sum_map_range, sum_sigma]
    exact sum_congr rfl fun b _ => sum_map_range _ _
  rw [e]
  have himg : ∑ b ∈ (range g).erase a, mu g D y a b κ =
      ∑ p ∈ ((range g).erase a).image fun b => (⟨max a b, min a b⟩ : Σ _ : ℕ, ℕ), mu g D y p.2 p.1 κ := by
    rw [sum_image]
    · refine sum_congr rfl fun b _ => ?_
      simp only [mu]
      rw [min_eq_left (min_le_max : min a b ≤ max a b), max_eq_right (min_le_max : min a b ≤ max a b)]
    · intro b _ b' _ hbb
      simp only [Sigma.mk.injEq, heq_eq_eq] at hbb
      omega
  rw [himg]
  refine sum_le_sum_of_subset ?_
  intro p hp
  obtain ⟨b, hb, rfl⟩ := mem_image.1 hp
  obtain ⟨hne, hb⟩ := mem_erase.1 hb
  have hb' := mem_range.1 hb
  exact mem_sigma.2 ⟨mem_range.2 (show max a b < g by omega), mem_range.2 (show min a b < max a b by omega)⟩

/-- Step 3, «The parameters»: «a setting of an admissible profile has at most (k + 1)M of them»
(marked incidences), for well-formed data, a node a < g and a setting z of the network of the
admissible profile y. -/
theorem marked_le {nb M : ℕ} {fl : Bool} (hW : WfD k n D) (h : admD k g n nb M D fl y = true) {a : ℕ} (ha : a < g) {z : List Bool}
    (hz : okD g n D y a z = true) : #(mk g n D a z) ≤ (k + 1) * M := by
  rcases (mk g n D a z).eq_empty_or_nonempty with h0 | ⟨o, ho⟩
  · rw [h0]
    exact Nat.zero_le _
  have hk : 1 ≤ k := by
    have h1 := clOf_wf hW (mem_range.1 (mem_filter.1 ho).1)
    have h2 := List.length_pos_iff.2 h1.1
    omega
  simp only [admD, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨_, h1⟩, h2⟩ := h
  have h3 := (h2 1 (by norm_num)).1
  have h4 : mu g D y a a 1 ≤ tot g D y 1 := by
    rw [tot, sum_map_range]
    exact single_le_sum (f := fun a => mu g D y a a 1) (fun _ _ => Nat.zero_le _) (mem_range.2 ha)
  have h5 := card_marked_le ha hz
  have h6 := sum_mu_le_totP (D := D) (y := y) ha 1
  have h7 : (k - 1 + 1) * tot g D y 1 ≤ k * M := by
    rw [Nat.sub_add_cancel hk]
    exact Nat.mul_le_mul_left _ h1
  have h8 : (k + 1) * M = k * M + M := by ring
  omega

/-! ### |σ_i| ≤ 2^i -/

/-- Step 3, «The parameters»: |σ_i| ≤ 2^i. -/
theorem abs_sig_le (i : ℕ) : |ParityChecks.sig i| ≤ 2 ^ i := by
  unfold ParityChecks.sig
  split_ifs with h
  · rw [h]
    simp
  · rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow, abs_two]
    exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)

/-- A product of numbers σ_(q_j) is at most 2 to the sum of the q_j in absolute value. -/
theorem abs_prod_sig_le (l : List ℕ) (q : ℕ → ℕ) : |(l.map fun j => ParityChecks.sig (q j)).prod| ≤ 2 ^ (l.map q).sum := by
  induction l with
  | nil => simp
  | cons j l ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.sum_cons, abs_mul, pow_add]
    exact mul_le_mul (abs_sig_le _) ih (abs_nonneg _) (by positivity)

/-- The numbers q_j of the checks with home a add up to at most the number of marked incidences that
touch a. -/
theorem sum_qj_le (a : ℕ) (z : List Bool) : ((((List.range D.2.length).filter fun j => home g j == a)).map (qj g n D a z)).sum ≤ #(mk g n D a z) := by
  have hq : ∀ j, qj g n D a z j = #((mk g n D a z).filter fun o => (obAt D o).2.2 = j) := by
    intro j
    refine length_filter_eq_card (nodup_tch a) _ _ fun e => ?_
    simp only [mem_tch, Bool.and_eq_true, beq_iff_eq, mk, mem_filter, mem_range]
    tauto
  rw [← List.sum_toFinset _ (List.Nodup.filter _ List.nodup_range), sum_congr rfl fun j _ => hq j, sum_card_fiberwise_eq_card_filter]
  exact card_filter_le _ _

/-- Step 3, «The parameters»: «condition (ii) holds with B = (k + 1)M + 1», for the weights: |W_a(z)|
≤ 2^B for g > 0 nodes, well-formed data, an admissible profile y, every node a < g and every word z. -/
public theorem abs_WD_le {k g n nb M : ℕ} {D : Dat} {fl : Bool} {y : ℕ} (_hg : 0 < g) (hW : WfD k n D) (h : admD k g n nb M D fl y = true) {a : ℕ} (ha : a < g)
    (z : List Bool) : |WD g n D y fl a z| ≤ 2 ^ BD k M := by
  unfold WD
  split_ifs with hz
  · have hs : |(bif fl then (-1 : ℤ) ^ ((tch g n D a).filter fun o => (obAt D o).1 == 0 && ownB g n D o a && mark g n D a z o).length else 1)| = 1 := by
      cases fl <;> simp
    rw [abs_mul, hs, mul_one]
    refine (abs_prod_sig_le _ _).trans (pow_le_pow_right₀ (by norm_num) ?_)
    have h1 := sum_qj_le (g := g) (n := n) (D := D) a z
    have h2 := marked_le hW h ha hz
    unfold BD
    omega
  · simp

/-! ### Display (69) -/

/-- g·⌈N/g⌉ ≤ N + g. -/
theorem mul_qv_le (g N : ℕ) : g * qv g N ≤ N + g := (Nat.mul_div_le _ _).trans (Nat.sub_le _ _)

/-- Display (69): gP ≤ 2(n + g)(1 + Δ(t̄ + 3)) + 2(10n + g)·s̄ + g, for g > 0, s̄ ≥ 0 and r̄ ≤ 10n,
with P = ⌈2P₀⌉ and P₀ = ⌈n/g⌉(1 + Δ(t̄ + 3)) + ⌈r̄/g⌉·s̄. -/
public theorem stP : StP := by
  intro g n Δ tb rb sb _ hsb hrb
  have hA : (0 : ℚ) ≤ 1 + Δ * (tb + 3) := by positivity
  have h0 : 0 ≤ 2 * P0 g n Δ tb rb sb := by
    unfold P0
    positivity
  have h1 : ((g : ℚ) * qv g n) ≤ n + g := by exact_mod_cast mul_qv_le g n
  have h2 : ((g : ℚ) * qv g rb) ≤ 10 * n + g := by
    have h : g * qv g rb ≤ 10 * n + g := (mul_qv_le g rb).trans (by omega)
    exact_mod_cast h
  have h3 : (PD g n Δ tb rb sb : ℚ) ≤ 2 * P0 g n Δ tb rb sb + 1 := (Nat.ceil_lt_add_one h0).le
  have h4 : (g : ℚ) * PD g n Δ tb rb sb ≤ g * (2 * P0 g n Δ tb rb sb + 1) := mul_le_mul_of_nonneg_left h3 (by positivity)
  have h5 := mul_le_mul_of_nonneg_right h1 hA
  have h6 := mul_le_mul_of_nonneg_right h2 hsb
  have h7 : (g : ℚ) * (2 * P0 g n Δ tb rb sb + 1) = 2 * ((g : ℚ) * qv g n * (1 + Δ * (tb + 3))) + 2 * ((g : ℚ) * qv g rb * sb) + g := by
    unfold P0
    ring
  push_cast
  linarith

end VariableBound.Net.SizeB
