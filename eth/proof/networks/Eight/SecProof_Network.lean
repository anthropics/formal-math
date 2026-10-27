/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.SecProof_NetworkDefs
public import SingleBitPieces.SecProof_Cost
import all StepMachines.Math.SatNet
import all StepMachines.Prog.CountNet
import all StepMachines.Prog.Count
import Mathlib.Tactic

/-! # Section 6 of the paper, «Proof of Theorem 2»: sentences on the network of Φ

The network of Φ is `Paper.networkOf g Φ` (proof/networks/Paper/SecProof_Proof.lean). This file
gives a statement of its own to sentences of the paragraphs «Clusters, occurrences, equality tests»
and «Cost», in the words defined in
proof/networks/Eight/SecProof_NetworkDefs.lean:
* «Hence Z is the number of assignments of the variables occurring in Φ that satisfy Φ»:
  `network_value_eq`;
* «An occurrence lies in at most two tests»: `card_tests_at_le_two`;
* «The total number of tests is the number of occurrences minus the number of variables that occur,
  hence at most 3m − 1»: `card_tests_add`, `card_tests_le`;
* «U counts each test between two clusters twice, so U ≤ 2(3m − 1) < 6m»: `network_total_eq`,
  `network_total_le_twice`, `network_total_lt`;
* «The remaining factor C₁2^{δ'g}(P + B)^{C₁}τ is polynomial in m, hence O(2^{δ'm/4})»:
  `remaining_factor`;
* the display of the exponent, with its strict inequality: `network_exponent_lt`.
Nothing here depends on Lemma 2 or on its pieces. -/

public section

namespace Eight

open Finset Groundwork Groundwork.Prog Groundwork.SatNet Paper

/-! ## «Z is the number of assignments of the variables occurring in Φ that satisfy Φ» -/

/-- A variable occurs in Φ if some literal of some clause of Φ is a literal of it. -/
theorem mem_occurring {Φ : Formula} {v : ℕ} : v ∈ occurring Φ ↔ ∃ C ∈ Φ, ∃ l ∈ C, l.1 = v := by
  simp only [occurring, List.mem_toFinset, List.mem_map, List.mem_flatten]
  constructor
  · rintro ⟨l, ⟨C, hC, hl⟩, rfl⟩
    exact ⟨C, hC, l, hl, rfl⟩
  · rintro ⟨C, hC, l, hl, rfl⟩
    exact ⟨l, ⟨C, hC, hl⟩, rfl⟩

theorem continued_of_mem {Φ : Formula} (a : Assignment Φ) {v : ℕ} (h : v ∈ occurring Φ) : continued a v = a ⟨v, h⟩ := dif_pos h

theorem continued_of_not_mem {Φ : Formula} (a : Assignment Φ) {v : ℕ} (h : v ∉ occurring Φ) : continued a v = false := dif_neg h

/-- **Section 6.** «Hence Z is the number of assignments of the variables occurring in Φ that
satisfy Φ.» Z is the value of the network of Φ on g ≥ 1 clusters; Φ has at most 3 literals per
clause. Same as in the paper.
(Empty clauses are allowed here; then both sides are 0.) The proof goes through the sentence before
it, «a term is 1 exactly if all occurrences of each variable carry the same bit and every clause has
a true occurrence»
(`Groundwork.SatNet.value_eq_card_good`), and a bijection between such terms and the satisfying
assignments. -/
theorem network_value_eq {g : ℕ} (hg : 0 < g) (Φ : Formula) (h3 : ∀ C ∈ Φ, C.length ≤ 3) : (networkOf g Φ).value = numSat Φ := by
  have hm := Count.le_mul_mu hg Φ
  rw [Count.value_wordNet hg, value_eq_card_good]
  congr 1
  symm
  have hmod : ∀ a : Assignment Φ, Satisfies Φ a → IsModel Φ (continued a) := by
    intro a ha
    refine ⟨fun C hC => ?_, fun v hv => continued_of_not_mem a fun h => ?_⟩
    · obtain ⟨l, hl, h, e⟩ := ha C hC
      exact ⟨l, hl, by rw [continued_of_mem a h, e]⟩
    · obtain ⟨C, hC, l, hl, e⟩ := mem_occurring.1 h
      exact hv C hC l hl e
  refine Finset.card_bij (fun a _ => toState Φ (continued a)) ?_ ?_ ?_
  · intro a ha
    simpa using good_toState h3 (hmod a (Finset.mem_filter.1 ha).2)
  · intro a ha a' ha' h
    have := toState_inj h3 hm (hmod a (Finset.mem_filter.1 ha).2) (hmod a' (Finset.mem_filter.1 ha').2) h
    funext v
    have h2 := congrFun this v.1
    rwa [continued_of_mem a v.2, continued_of_mem a' v.2] at h2
  · intro z hz
    obtain ⟨a, ha, rfl⟩ := exists_model hm (Finset.mem_filter.1 hz).2
    have he : continued (Φ := Φ) (fun v => a v.1) = a := by
      funext v
      by_cases h : v ∈ occurring Φ
      · exact continued_of_mem _ h
      · rw [continued_of_not_mem _ h]
        exact (ha.2 v fun C hC l hl e => h (mem_occurring.2 ⟨C, hC, l, hl, e⟩)).symm
    refine ⟨fun v => a v.1, ?_, by rw [he]⟩
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun C hC => ?_⟩
    obtain ⟨l, hl, e⟩ := ha.1 C hC
    exact ⟨l, hl, mem_occurring.2 ⟨C, hC, l, hl, rfl⟩, e⟩

/-- The formula without clauses: no variable occurs, and the one assignment of no variables
satisfies it. -/
theorem numSat_nil : numSat [] = 1 := by
  have h : ∀ a : Assignment [], Satisfies [] a := fun a C hC => absurd hC (List.not_mem_nil)
  have hE : IsEmpty {v : ℕ // v ∈ occurring []} := ⟨fun v => by simpa [occurring] using v.2⟩
  unfold numSat
  rw [Finset.filter_true_of_mem fun a _ => h a, Finset.card_univ, Fintype.card_eq_one_iff]
  exact ⟨fun v => (hE.false v).elim, fun a => funext fun v => (hE.false v).elim⟩

/-- «… and Φ is satisfiable if and only if Z > 0», read off the count: some assignment of the
occurring variables satisfies Φ exactly if some assignment of all variables does. -/
theorem numSat_pos_iff (Φ : Formula) : 0 < numSat Φ ↔ Φ.Sat := by
  unfold numSat
  rw [Finset.card_pos]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨continued a, fun C hC => ?_⟩
    obtain ⟨l, hl, h, e⟩ := (Finset.mem_filter.1 ha).2 C hC
    exact ⟨l, hl, by rw [continued_of_mem a h, e]⟩
  · rintro ⟨a, ha⟩
    refine ⟨fun v => a v.1, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun C hC => ?_⟩⟩
    obtain ⟨l, hl, e⟩ := ha C hC
    exact ⟨l, hl, mem_occurring.2 ⟨C, hC, l, hl, rfl⟩, e⟩

/-! ## «Clusters, occurrences, equality tests»: the number of tests, and the total U -/

section Tests

variable {Φ : Formula} {g μ k : ℕ}

theorem mem_occurrencesOf {p : Slot g μ k} : p ∈ occurrencesOf Φ g μ k ↔ lit Φ p ≠ none := by simp [occurrencesOf]

theorem mem_testsOf {t : Slot g μ k × Slot g μ k} : t ∈ testsOf Φ g μ k ↔ Link Φ t.1 t.2 := by simp [testsOf]

/-- An occurrence with an earlier occurrence of the same variable is the second occurrence of a
test. -/
theorem exists_link_of_earlier {p₀ q : Slot g μ k} (h1 : idx p₀ < idx q) (h2 : lab Φ p₀ = lab Φ q) (h3 : lab Φ q ≠ none) : ∃ p, Link Φ p q := by
  obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image ({r : Slot g μ k | idx r < idx q ∧ lab Φ r = lab Φ q} : Finset (Slot g μ k)) idx ⟨p₀, by simp [h1, h2]⟩
  have hp' : idx p < idx q ∧ lab Φ p = lab Φ q := by simpa using hp
  refine ⟨p, hp'.1, by rw [hp'.2]; exact h3, hp'.2, fun r hr1 hr2 hr3 => ?_⟩
  have := hmax r (by simp [hr2, hr3.trans hp'.2])
  omega

/-- «An occurrence lies in at most two tests.» Same as in the paper. -/
theorem card_tests_at_le_two (o : Slot g μ k) : #{t ∈ testsOf Φ g μ k | t.1 = o ∨ t.2 = o} ≤ 2 := by
  rw [Finset.filter_or]
  refine (Finset.card_union_le _ _).trans ?_
  have h1 : #{t ∈ testsOf Φ g μ k | t.1 = o} ≤ 1 := by
    refine Finset.card_le_one.2 fun t ht t' ht' => ?_
    obtain ⟨h, e⟩ := Finset.mem_filter.1 ht
    obtain ⟨h', e'⟩ := Finset.mem_filter.1 ht'
    have l := mem_testsOf.1 h
    have l' := mem_testsOf.1 h'
    rw [e] at l
    rw [e'] at l'
    exact Prod.ext (e.trans e'.symm) (l.succ_unique idx_injective l')
  have h2 : #{t ∈ testsOf Φ g μ k | t.2 = o} ≤ 1 := by
    refine Finset.card_le_one.2 fun t ht t' ht' => ?_
    obtain ⟨h, e⟩ := Finset.mem_filter.1 ht
    obtain ⟨h', e'⟩ := Finset.mem_filter.1 ht'
    have l := mem_testsOf.1 h
    have l' := mem_testsOf.1 h'
    rw [e] at l
    rw [e'] at l'
    exact Prod.ext (l.pred_unique idx_injective l') (e.trans e'.symm)
  omega

/-- There are as many tests as occurrences that are not the first of their variable. -/
theorem card_testsOf_eq : #(testsOf Φ g μ k) = #{q ∈ occurrencesOf Φ g μ k | ∃ p, Link Φ p q} := by
  refine Finset.card_bij (fun t _ => t.2) ?_ ?_ ?_
  · intro t ht
    have l := mem_testsOf.1 ht
    exact Finset.mem_filter.2 ⟨mem_occurrencesOf.2 l.used_right, t.1, l⟩
  · intro t ht t' ht' e
    have l := mem_testsOf.1 ht
    have l' := mem_testsOf.1 ht'
    have e : t.2 = t'.2 := e
    rw [e] at l
    exact Prod.ext (l.pred_unique idx_injective l') e
  · intro q hq
    obtain ⟨p, l⟩ := (Finset.mem_filter.1 hq).2
    exact ⟨(p, q), mem_testsOf.2 l, rfl⟩

/-- There are as many first occurrences as variables that occur. -/
theorem card_first_eq (hk : ∀ C ∈ Φ, C.length ≤ k) (hm : Φ.length ≤ g * μ) : #{q ∈ occurrencesOf Φ g μ k | ¬ ∃ p, Link Φ p q} = #(occurring Φ) := by
  have hlab : ∀ q ∈ occurrencesOf Φ g μ k, ∃ l, lit Φ q = some l ∧ lab Φ q = some l.1 := by
    intro q hq
    obtain ⟨l, hl⟩ := Option.ne_none_iff_exists'.1 (mem_occurrencesOf.1 hq)
    exact ⟨l, hl, by simp [lab, hl]⟩
  refine Finset.card_bij (fun q _ => (lab Φ q).getD 0) ?_ ?_ ?_
  · intro q hq
    obtain ⟨l, hl, hv⟩ := hlab q (Finset.mem_filter.1 hq).1
    obtain ⟨C, hC, hlC⟩ := lit_mem hl
    simp only [hv, Option.getD_some]
    exact mem_occurring.2 ⟨C, hC, l, hlC, rfl⟩
  · intro q hq q' hq' e
    obtain ⟨l, -, hv⟩ := hlab q (Finset.mem_filter.1 hq).1
    obtain ⟨l', -, hv'⟩ := hlab q' (Finset.mem_filter.1 hq').1
    simp only [hv, hv', Option.getD_some] at e
    have hqq : lab Φ q = lab Φ q' := by rw [hv, hv', e]
    rcases lt_trichotomy (idx q) (idx q') with h | h | h
    · exact absurd (exists_link_of_earlier h hqq (by simp [hv'])) (Finset.mem_filter.1 hq').2
    · exact idx_injective h
    · exact absurd (exists_link_of_earlier h hqq.symm (by simp [hv])) (Finset.mem_filter.1 hq).2
  · intro v hv
    obtain ⟨C, hC, l, hl, rfl⟩ := mem_occurring.1 hv
    obtain ⟨p₀, hp₀⟩ := exists_slot (g := g) (μ := μ) hk hm hC hl
    obtain ⟨q, hq, hmin⟩ := Finset.exists_min_image ({r : Slot g μ k | lab Φ r = some l.1} : Finset (Slot g μ k)) idx
      ⟨p₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [lab, hp₀]; rfl⟩⟩
    have hq' : lab Φ q = some l.1 := by simpa using hq
    refine ⟨q, Finset.mem_filter.2 ⟨mem_occurrencesOf.2 fun h => ?_, ?_⟩, by simp [hq']⟩
    · simp [lab, h] at hq'
    · rintro ⟨p, hp⟩
      have := hmin p (by simp [hp.2.2.1, hq'])
      have := hp.1
      omega

/-- «The total number of tests is the number of occurrences minus the number of variables that
occur», written without subtraction. -/
theorem card_testsOf_add (hk : ∀ C ∈ Φ, C.length ≤ k) (hm : Φ.length ≤ g * μ) : #(testsOf Φ g μ k) + #(occurring Φ) = #(occurrencesOf Φ g μ k) := by
  rw [card_testsOf_eq, ← card_first_eq hk hm]
  exact Finset.card_filter_add_card_filter_not _

/-- The tests from cluster a to cluster b, counted by their first occurrences. -/
theorem card_out_eq (a b : Fin g) : #{s : Sl μ k | Out Φ a b s} = #{t ∈ testsOf Φ g μ k | t.1.1 = a ∧ t.2.1 = b} := by
  symm
  refine Finset.card_bij (fun t _ => t.1.2) ?_ ?_ ?_
  · rintro ⟨⟨a', s⟩, ⟨b', s'⟩⟩ ht
    obtain ⟨h, e1, e2⟩ := Finset.mem_filter.1 ht
    simp only at e1 e2
    subst e1 e2
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, s', mem_testsOf.1 h⟩
  · rintro ⟨⟨a', s⟩, ⟨b', s'⟩⟩ ht ⟨⟨a'', r⟩, ⟨b'', r'⟩⟩ ht' e
    obtain ⟨h, e1, e2⟩ := Finset.mem_filter.1 ht
    obtain ⟨h', e1', e2'⟩ := Finset.mem_filter.1 ht'
    simp only at e1 e2 e1' e2' e
    subst e1 e2 e1' e2' e
    have l : Link Φ (a'', s) (b'', s') := mem_testsOf.1 h
    have l' : Link Φ (a'', s) (b'', r') := mem_testsOf.1 h'
    rw [l.succ_unique idx_injective l']
  · intro s hs
    obtain ⟨s', l⟩ := (Finset.mem_filter.1 hs).2
    exact ⟨((a, s), (b, s')), Finset.mem_filter.2 ⟨mem_testsOf.2 l, rfl, rfl⟩, rfl⟩

/-- No test leads from a cluster to an earlier one: the earlier occurrence comes first. -/
theorem card_tests_back_eq_zero {a b : Fin g} (h : a < b) : #{t ∈ testsOf Φ g μ k | t.1.1 = b ∧ t.2.1 = a} = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro t ht ⟨e1, e2⟩
  have := (mem_testsOf.1 ht).fst_le
  rw [e1, e2] at this
  exact absurd h (not_lt.2 this)

theorem c_net_eq_add {a b : Fin g} (hab : a ≠ b) :
    (net Φ g μ k).c a b = #{t ∈ testsOf Φ g μ k | t.1.1 = a ∧ t.2.1 = b} + #{t ∈ testsOf Φ g μ k | t.1.1 = b ∧ t.2.1 = a} := by
  simp only [net]
  rcases lt_or_gt_of_ne hab with h | h
  · rw [min_eq_left h.le, max_eq_right h.le, card_out_eq, card_tests_back_eq_zero h, Nat.add_zero]
  · rw [min_eq_right h.le, max_eq_left h.le, card_out_eq, card_tests_back_eq_zero h, Nat.zero_add]

/-- The tests between two different clusters, sorted by the cluster of the first and the cluster of
the second occurrence. -/
theorem sum_card_tests_eq : ∑ a : Fin g, ∑ b ∈ univ.erase a, #{t ∈ testsOf Φ g μ k | t.1.1 = a ∧ t.2.1 = b} = #{t ∈ testsOf Φ g μ k | t.1.1 ≠ t.2.1} := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun t => t.1.1) (t := univ) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.card_eq_sum_card_fiberwise (f := fun t => t.2.1) (t := univ.erase a)]
  · refine Finset.sum_congr rfl fun b hb => ?_
    congr 1
    ext t
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨h, e1, e2⟩
      exact ⟨⟨⟨h, by rw [e1, e2]; exact (Finset.ne_of_mem_erase hb).symm⟩, e1⟩, e2⟩
    · rintro ⟨⟨⟨h, -⟩, e1⟩, e2⟩
      exact ⟨h, e1, e2⟩
  · intro t ht
    obtain ⟨h, e⟩ := Finset.mem_filter.1 (Finset.mem_coe.1 ht)
    have hne := (Finset.mem_filter.1 h).2
    exact Finset.mem_coe.2 (Finset.mem_erase.2 ⟨fun e' => hne (e.trans e'.symm), Finset.mem_univ _⟩)

/-- «U counts each test between two clusters twice», for the network on functions
(`Groundwork.SatNet.net`). -/
theorem U_net_eq : (net Φ g μ k).U = 2 * #{t ∈ testsOf Φ g μ k | t.1.1 ≠ t.2.1} := by
  unfold Network.U
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => c_net_eq_add (Φ := Φ) (μ := μ) (k := k) (Finset.ne_of_mem_erase hb).symm]
  simp only [Finset.sum_add_distrib]
  have h2 : ∑ a : Fin g, ∑ b ∈ univ.erase a, #{t ∈ testsOf Φ g μ k | t.1.1 = b ∧ t.2.1 = a} =
      ∑ b : Fin g, ∑ a ∈ univ.erase b, #{t ∈ testsOf Φ g μ k | t.1.1 = b ∧ t.2.1 = a} :=
    Finset.sum_comm' fun a b => by simp [ne_comm]
  rw [h2, sum_card_tests_eq]
  ring

end Tests

/-! ### The same for the network of Φ on g clusters -/

/-- At most 3 occurrences per clause. -/
theorem card_occurrences_le (g : ℕ) (Φ : Formula) : #(occurrences g Φ) ≤ 3 * Φ.length := by
  have h := card_used_le (φ := Φ) (g := g) (μ := clusterSize g Φ) (k := 3)
  have e : occurrences g Φ = ({p : Slot g (clusterSize g Φ) 3 | lit Φ p ≠ none} : Finset _) := rfl
  rw [e]
  omega

/-- **Section 6.** «The total number of tests is the number of occurrences minus the number of
variables that occur». Same as in the paper; written without subtraction. -/
theorem card_tests_add {g : ℕ} (hg : 0 < g) {Φ : Formula} (h3 : ∀ C ∈ Φ, C.length ≤ 3) : #(tests g Φ) + #(occurring Φ) = #(occurrences g Φ) :=
  card_testsOf_add h3 (Count.le_mul_mu hg Φ)

/-- **Section 6.** «… hence at most 3m − 1», for m ≥ 1. Same as in the paper (also if some clauses
are empty). -/
theorem card_tests_le {g : ℕ} (hg : 0 < g) {Φ : Formula} (h3 : ∀ C ∈ Φ, C.length ≤ 3) (hm : 1 ≤ Φ.length) : #(tests g Φ) ≤ 3 * Φ.length - 1 := by
  have h1 := card_tests_add hg h3
  have h2 := card_occurrences_le g Φ
  have h4 : 0 < #(occurrences g Φ) → 0 < #(occurring Φ) := by
    intro h
    obtain ⟨p, hp⟩ := Finset.card_pos.1 h
    obtain ⟨l, hl⟩ := Option.ne_none_iff_exists'.1 (mem_occurrencesOf.1 hp)
    obtain ⟨C, hC, hlC⟩ := lit_mem hl
    exact Finset.card_pos.2 ⟨l.1, mem_occurring.2 ⟨C, hC, l, hlC, rfl⟩⟩
  omega

/-- **Section 6, «Cost».** «U counts each test between two clusters twice». Same as in the paper. -/
theorem network_total_eq {g : ℕ} (hg : 0 < g) (Φ : Formula) : (networkOf g Φ).U = 2 * #{t ∈ tests g Φ | t.1.1 ≠ t.2.1} := by
  rw [Count.U_wordNet hg]
  exact U_net_eq

/-- **Section 6, «Cost».** «… so U ≤ 2(3m − 1)», for m ≥ 1. Same as in the paper. -/
theorem network_total_le_twice {g : ℕ} (hg : 0 < g) {Φ : Formula} (h3 : ∀ C ∈ Φ, C.length ≤ 3) (hm : 1 ≤ Φ.length) : (networkOf g Φ).U ≤ 2 * (3 * Φ.length - 1) := by
  rw [network_total_eq hg]
  exact Nat.mul_le_mul_left 2 ((Finset.card_filter_le _ _).trans (card_tests_le hg h3 hm))

/-- **Section 6, «Cost».** «… < 6m», for m ≥ 1. Same as in the paper. -/
theorem network_total_lt {g : ℕ} (hg : 0 < g) {Φ : Formula} (h3 : ∀ C ∈ Φ, C.length ≤ 3) (hm : 1 ≤ Φ.length) : (networkOf g Φ).U < 6 * Φ.length := by
  have := network_total_le_twice hg h3 hm
  omega

/-- For m = 0 there is no test, and U = 0. -/
theorem network_total_nil {g : ℕ} (hg : 0 < g) : (networkOf g []).U = 0 := by
  have := Paper.network_total_le hg []
  simpa using this

/-! ## «The remaining factor … is polynomial in m, hence O(2^{δ'm/4})» -/

/-- **Section 6, «Cost».** «The remaining factor C₁2^{δ'g}(P + B)^{C₁}τ is polynomial in m, hence
O(2^{δ'm/4})», with P = 6m̄, m̄ = ⌈m/g⌉ (written (m + g − 1)/g), B = 1 and a cost τ ≤ c(m + 1)^c of
a query: for all C₁, c, g and δ' > 0 there is a constant A with C₁·2^{δ'g}·(6m̄ + 1)^{C₁}·c(m + 1)^c
≤ A·2^{δ'm/4} for every m. Same as in the paper, with «polynomial in m» for τ made explicit. -/
theorem remaining_factor_query (C₁ c g : ℕ) {δ' : ℝ} (hδ' : 0 < δ') : ∃ A : ℕ, ∀ m : ℕ,
    (C₁ : ℝ) * (2 : ℝ) ^ (δ' * g) * ((6 * ((m + g - 1) / g) + 1 : ℕ) : ℝ) ^ C₁ * (c * ((m : ℝ) + 1) ^ c) ≤ A * (2 : ℝ) ^ (δ' * m / 4) := by
  obtain ⟨D, hD⟩ := SatNet.pow_le_two_rpow (C₁ + c) (c := δ' / 4) (by positivity)
  refine ⟨⌈(C₁ : ℝ) * (2 : ℝ) ^ (δ' * g) * 7 ^ C₁ * c * D * (2 : ℝ) ^ (δ' / 4)⌉₊, fun m => ?_⟩
  have hdiv : (m + g - 1) / g ≤ m := by
    rcases Nat.eq_zero_or_pos g with rfl | hg
    · simp
    · rw [Nat.div_le_iff_le_mul_add_pred hg]
      have : m ≤ g * m := Nat.le_mul_of_pos_left _ hg
      omega
  have hP : ((6 * ((m + g - 1) / g) + 1 : ℕ) : ℝ) ≤ 7 * ((m : ℝ) + 1) := by
    have : 6 * ((m + g - 1) / g) + 1 ≤ 7 * (m + 1) := by omega
    exact_mod_cast this
  have hpow : ((m : ℝ) + 1) ^ (C₁ + c) ≤ D * ((2 : ℝ) ^ (δ' / 4) * (2 : ℝ) ^ (δ' * m / 4)) := by
    have h := hD (m + 1)
    rw [← Real.rpow_add two_pos]
    have e : δ' / 4 * ((m + 1 : ℕ) : ℝ) = δ' / 4 + δ' * m / 4 := by push_cast; ring
    rw [e] at h
    exact_mod_cast h
  calc (C₁ : ℝ) * (2 : ℝ) ^ (δ' * g) * ((6 * ((m + g - 1) / g) + 1 : ℕ) : ℝ) ^ C₁ * (c * ((m : ℝ) + 1) ^ c)
      ≤ (C₁ : ℝ) * (2 : ℝ) ^ (δ' * g) * (7 * ((m : ℝ) + 1)) ^ C₁ * (c * ((m : ℝ) + 1) ^ c) := by gcongr
    _ = (C₁ : ℝ) * (2 : ℝ) ^ (δ' * g) * 7 ^ C₁ * c * ((m : ℝ) + 1) ^ (C₁ + c) := by rw [mul_pow, pow_add]; ring
    _ ≤ (C₁ : ℝ) * (2 : ℝ) ^ (δ' * g) * 7 ^ C₁ * c * (D * ((2 : ℝ) ^ (δ' / 4) * (2 : ℝ) ^ (δ' * m / 4))) := by gcongr
    _ = (C₁ : ℝ) * (2 : ℝ) ^ (δ' * g) * 7 ^ C₁ * c * D * (2 : ℝ) ^ (δ' / 4) * (2 : ℝ) ^ (δ' * m / 4) := by ring
    _ ≤ _ := by
        gcongr
        exact Nat.le_ceil _

/-- The same with τ = 1, the cost of a query to the network of Φ in the model used here (a value of
W or f is computed in one step; that these steps take polynomial time is
`Groundwork.Prog.satP_keeps`):
C₁·2^{δ'g}·(6⌈m/g⌉ + 1)^{C₁} ≤ A·2^{δ'm/4} for every m. -/
theorem remaining_factor (C₁ g : ℕ) {δ' : ℝ} (hδ' : 0 < δ') : ∃ A : ℕ, ∀ m : ℕ,
    (C₁ : ℝ) * (2 : ℝ) ^ (δ' * g) * ((6 * ((m + g - 1) / g) + 1 : ℕ) : ℝ) ^ C₁ ≤ A * (2 : ℝ) ^ (δ' * m / 4) := by
  obtain ⟨A, hA⟩ := remaining_factor_query C₁ 1 g hδ'
  refine ⟨A, fun m => le_trans ?_ (hA m)⟩
  have h0 : (0 : ℝ) ≤ (C₁ : ℝ) * (2 : ℝ) ^ (δ' * g) * ((6 * ((m + g - 1) / g) + 1 : ℕ) : ℝ) ^ C₁ := by positivity
  have h1 : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) * ((m : ℝ) + 1) ^ 1 := by
    have : (0 : ℝ) ≤ m := by positivity
    push_cast
    linarith
  exact le_mul_of_one_le_right h0 h1

/-! ## «Cost»: the exponent -/

/-- **Section 6, «Cost».** «With e = δ'/12, K ≥ 72 and 1/K ≤ δ'/72, the exponent in Lemma 1 is eU +
e·gP/K + 2gP/K < ½δ'm + (1/144)δ'(m + g) + (1/6)δ'(m + g) = (97/144)δ'm + (25/144)δ'g», from U < 6m
and gP ≤ 6(m + g). Same as in the
paper, with the strict inequality. K ≥ 72 follows from K ≥ 72/δ' and δ' ≤ 1. -/
theorem network_exponent_lt {δ' : ℝ} {K U g P m : ℕ} (hδ' : 0 < δ') (h1 : δ' ≤ 1) (hK : 72 / δ' ≤ K) (hU : U < 6 * m) (hP : g * P ≤ 6 * (m + g)) :
    δ' / 12 * ((U : ℝ) + (g : ℝ) * P / K) + 2 * (g : ℝ) * P / K < 97 / 144 * δ' * m + 25 / 144 * δ' * g := by
  have h := SingleBitPieces.network_exponent_le (U := U + 1) hδ' h1 hK hU hP
  push_cast at h
  nlinarith

/-- «… ≤ ¾δ'm + δ'g.» -/
theorem network_exponent_lt' {δ' : ℝ} {K U g P m : ℕ} (hδ' : 0 < δ') (h1 : δ' ≤ 1) (hK : 72 / δ' ≤ K) (hU : U < 6 * m) (hP : g * P ≤ 6 * (m + g)) :
    δ' / 12 * ((U : ℝ) + (g : ℝ) * P / K) + 2 * (g : ℝ) * P / K < 3 / 4 * δ' * m + δ' * g := by
  have h := network_exponent_lt hδ' h1 hK hU hP
  have hm : (0 : ℝ) ≤ δ' * m := by positivity
  have hg : (0 : ℝ) ≤ δ' * g := by positivity
  nlinarith

end Eight
