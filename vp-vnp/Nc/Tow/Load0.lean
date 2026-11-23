/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Load2

/-!
# The tower plan: the loads after the start
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b D J r m Uu AA : ℕ} {T : Tower h b D J r} {R : Routes T m Uu}
  {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {lhat : ℕ} {n : Fin AA → Fin AA → ℕ}
  {o : NM R FL (ch := ch) → ℕ}

/-- The number of units of a batch. -/
noncomputable def Bt (T : Tower h b D J r) (ch : Fin AA ↪ T.X 0) (lhat : ℕ) (n : Fin AA → Fin AA → ℕ) (a c : Fin AA)
    (γ : T.X 0) : ℕ :=
  if Valid lhat n then ((range (n a c)).filter fun k => gam T ch a k = γ).card else 0

theorem Bt_le (a c : Fin AA) (γ : T.X 0) : Bt T ch lhat n a c γ ≤ n a c / Fintype.card (T.X 0) + 1 := by
  unfold Bt
  split_ifs
  · have hX : 0 < Fintype.card (T.X 0) := Fintype.card_pos_iff.2 ⟨ch a⟩
    rw [← card_range (n a c / Fintype.card (T.X 0) + 1)]
    refine card_le_card_of_injOn (fun k => k / Fintype.card (T.X 0)) ?_ ?_
    · intro k hk
      have h1 := mem_range.1 (mem_filter.1 (mem_coe.1 hk)).1
      exact mem_coe.2 (mem_range.2 (Nat.lt_succ_of_le (Nat.div_le_div_right h1.le)))
    · intro k hk k' hk' heq
      have h1 := (mem_filter.1 (mem_coe.1 hk)).2
      have h2 := (mem_filter.1 (mem_coe.1 hk')).2
      have h3 : gam T ch a k = gam T ch a k' := h1.trans h2.symm
      unfold gam at h3
      have h4 := (Fintype.equivFin (T.X 0)).symm.injective h3
      have h5 : k % Fintype.card (T.X 0) = k' % Fintype.card (T.X 0) := congrArg Fin.val h4
      simp only at heq
      rw [← Nat.div_add_mod k (Fintype.card (T.X 0)), ← Nat.div_add_mod k' (Fintype.card (T.X 0)), heq, h5]
  · exact Nat.zero_le _

theorem bt_start (a c : Fin AA) (γ : T.X 0) (s : Fin (2 * m)) :
    bt R ch lhat n (.nxt (.start a c γ s) : Tg T m AA) ≤ if s.1 = 0 then Bt T ch lhat n a c γ else 0 := by
  classical
  unfold bt Bt
  by_cases hv : Valid lhat n
  · rw [if_pos hv]
    have h1 : ∀ a' c', ((range (n a' c')).filter fun k => tgB T R ch a' c' k = .nxt (.start a c γ s)).card ≤
        if a' = a ∧ c' = c then (if s.1 = 0 then ((range (n a c)).filter fun k => gam T ch a k = γ).card else 0) else 0 := by
      intro a' c'
      by_cases hac : a' = a ∧ c' = c
      · obtain ⟨rfl, rfl⟩ := hac
        rw [if_pos ⟨rfl, rfl⟩]
        by_cases hs : s.1 = 0
        · rw [if_pos hs]
          refine card_le_card fun k hk => ?_
          obtain ⟨h2, h3⟩ := mem_filter.1 hk
          refine mem_filter.2 ⟨h2, ?_⟩
          rcases tgB_cases (R := R) (ch := ch) a' c' k with h1 | ⟨hm, h1⟩ | ⟨e', -, h1, -⟩ <;> rw [h1] at h3
          · simp at h3
          · simp only [Tg.nxt.injEq, RM.start.injEq] at h3
            exact h3.2.2.1
          · simp at h3
        · rw [if_neg hs, Nat.le_zero, card_eq_zero]
          refine filter_false_of_mem fun k _ h3 => ?_
          rcases tgB_cases (R := R) (ch := ch) a' c' k with h1 | ⟨hm, h1⟩ | ⟨e', -, h1, -⟩ <;> rw [h1] at h3
          · simp at h3
          · simp only [Tg.nxt.injEq, RM.start.injEq] at h3
            exact hs (congrArg Fin.val h3.2.2.2).symm
          · simp at h3
      · rw [if_neg hac, Nat.le_zero, card_eq_zero]
        refine filter_false_of_mem fun k _ h3 => ?_
        rcases tgB_cases (R := R) (ch := ch) a' c' k with h1 | ⟨hm, h1⟩ | ⟨e', -, h1, -⟩ <;> rw [h1] at h3
        · simp at h3
        · simp only [Tg.nxt.injEq, RM.start.injEq] at h3
          exact hac ⟨h3.1, h3.2.1⟩
        · simp at h3
    refine (Finset.sum_le_sum fun a' _ => Finset.sum_le_sum fun c' _ => h1 a' c').trans ?_
    rw [Finset.sum_eq_single a, Finset.sum_eq_single c]
    · rw [if_pos ⟨rfl, rfl⟩, if_pos hv]
    · intro c' _ hc'
      rw [if_neg fun hh => hc' hh.2]
    · intro hn; exact absurd (mem_univ _) hn
    · intro a' _ ha'
      exact Finset.sum_eq_zero fun c' _ => if_neg fun hh => ha' hh.1
    · intro hn; exact absurd (mem_univ _) hn
  · rw [if_neg hv]
    exact Nat.zero_le _

theorem tgR_start {x : RM T m AA} {ν : Bool} {a c : Fin AA} {γ : T.X 0} {s : Fin (2 * m)}
    (hx : tgR T R ch x ν = .nxt (.start a c γ s)) : ν = true ∧ ∃ s' : Fin (2 * m), x = .start a c γ s' ∧ s.1 = s'.1 + 1 := by
  rcases x with ⟨a', c', γ', s'⟩ | ⟨j', i', e'⟩ | ⟨j', e', s'⟩ | e'
  · have this : ∀ e' : Option (T.Ed 0), (edgeO T e' : Tg T m AA) ≠ .nxt (.start a c γ s) := by
      intro e' he
      cases e' <;> simp [edgeO] at he
    cases ν
    · exact absurd hx (this _)
    · simp only [tgR] at hx
      split_ifs at hx with hs
      · simp only [Tg.nxt.injEq, RM.start.injEq] at hx
        obtain ⟨h1, h2, h3, h4⟩ := hx
        subst h1 h2 h3
        exact ⟨rfl, s', rfl, (congrArg Fin.val h4).symm⟩
      · exact absurd hx (this _)
  · simp [tgR] at hx
  · cases ν
    · fin_cases s' <;> simp [tgR] at hx
    · fin_cases s'
      · simp only [tgR, Fin.zero_eta, Matrix.cons_val_zero] at hx
        split_ifs at hx <;> simp at hx
      · simp [tgR] at hx
      · simp only [tgR, Fin.reduceFinMk, Matrix.cons_val] at hx
        split_ifs at hx
        simp at hx
      · simp [tgR] at hx
  · simp [tgR] at hx

section

variable (hr : 0 < r) (hb : 0 < b)
include hr hb

theorem num_start_le (a c : Fin AA) (γ : T.X 0) (s : Fin (2 * m)) (hx : okR T R ch (.start a c γ s)) :
    num R ch FL lhat n o (.inl ⟨.start a c γ s, hx⟩) ≤ Bt T ch lhat n a c γ := by
  classical
  obtain ⟨s, hs⟩ := s
  induction s with
  | zero =>
    have h1 : num R ch FL lhat n o (.inl ⟨.start a c γ ⟨0, hs⟩, hx⟩) ≤
        load R ch FL lhat n o (.nxt (.start a c γ ⟨0, hs⟩)) := by
      rw [num_eq hr hb, numF]
      split_ifs
      · exact le_rfl
      · exact Nat.zero_le _
    refine h1.trans ?_
    rw [load_def, Finset.sum_eq_zero]
    · exact (bt_start a c γ ⟨0, hs⟩).trans (by simp)
    · rintro ⟨⟨x, hx'⟩ | l, ν⟩ _
      · rw [if_neg]
        intro hν
        obtain ⟨-, s', -, h3⟩ := tgR_start (x := x) (ν := ν) hν
        simp at h3
      · rw [if_neg]
        intro hν
        simp [tgM] at hν
  | succ s ih =>
    have hs0 : s < 2 * m := by omega
    have hx0 : okR T R ch (.start a c γ ⟨s, hs0⟩) := by
      obtain ⟨h1, h2⟩ := hx
      exact ⟨h1, by simp only at h2 ⊢; omega⟩
    have h1 : num R ch FL lhat n o (.inl ⟨.start a c γ ⟨s + 1, hs⟩, hx⟩) ≤
        load R ch FL lhat n o (.nxt (.start a c γ ⟨s + 1, hs⟩)) := by
      rw [num_eq hr hb, numF]
      split_ifs
      · exact le_rfl
      · exact Nat.zero_le _
    refine h1.trans ?_
    have hbt : bt R ch lhat n (.nxt (.start a c γ ⟨s + 1, hs⟩) : Tg T m AA) = 0 := by
      have := bt_start (R := R) (ch := ch) (lhat := lhat) (n := n) a c γ ⟨s + 1, hs⟩
      rw [if_neg (by simp)] at this
      omega
    refine (load_le_sum {(⟨.inl ⟨.start a c γ ⟨s, hs0⟩, hx0⟩, true⟩ : NM R FL (ch := ch))} hbt ?_).trans ?_
    · rintro ⟨⟨x, hx'⟩ | l, ν⟩ hν -
      · obtain ⟨h2, s', h3, h4⟩ := tgR_start (x := x) (ν := ν) hν
        have h2 : ν = true := h2
        subst h2
        have h4 : s + 1 = s'.1 + 1 := h4
        have h5 : s' = ⟨s, hs0⟩ := Fin.ext (by change s'.1 = s; omega)
        subst h5
        subst h3
        exact mem_singleton_self _
      · simp [tgM] at hν
    · rw [Finset.sum_singleton]
      exact (alv_le_num hr hb _ _).trans (ih hs0 hx0)

end

theorem card_filter_getElem {α : Type*} [DecidableEq α] (l : List α) (e : α) :
    ((range l.length).filter fun p => l[p]? = some e).card = l.count e := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, List.count_cons, ← ih, card_filter, card_filter, Finset.sum_range_succ']
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq]
    congr 1
    by_cases h1 : a = e <;> simp [h1]

/-- The steps of a path on an edge. -/
theorem steps_le {α : Type*} [DecidableEq α] (l : List α) (e : α) (L M : ℕ) (hL : 0 < L) (hLl : L ≤ l.length) :
    (∑ s ∈ range M, ((if s + 1 < L ∧ l[s]? = some e then 1 else 0) +
      if s + 2 = L ∧ l[s + 1]? = some e then 1 else 0)) + (if L ≤ 1 ∧ l[0]? = some e then 1 else 0) ≤ l.count e := by
  rw [← card_filter_getElem]
  have h1 : ((range L).filter fun p => l[p]? = some e).card ≤ ((range l.length).filter fun p => l[p]? = some e).card :=
    card_le_card (filter_subset_filter _ (range_subset_range.2 hLl))
  refine le_trans ?_ h1
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  rw [card_filter, Finset.sum_range_succ, Finset.sum_add_distrib, add_assoc]
  refine add_le_add ?_ ?_
  · have h2 : ∀ s ∈ range M, (if s + 1 < L' + 1 ∧ l[s]? = some e then 1 else 0) =
        if s ∈ range L' then (if l[s]? = some e then 1 else 0) else 0 := by
      intro s _
      by_cases hs : s < L'
      · simp [hs]
      · simp [hs]
    rw [Finset.sum_congr rfl h2, ← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset fun s hs => (mem_filter.1 hs).2
  · by_cases hc : l[L']? = some e
    · rw [if_pos hc]
      by_cases h0 : L' = 0
      · subst h0
        rw [Finset.sum_eq_zero]
        · simp [hc]
        · intro s _
          rw [if_neg]
          omega
      · rw [if_neg (by omega : ¬ (L' + 1 ≤ 1 ∧ l[0]? = some e)), add_zero]
        have h3 : ∀ s ∈ range M, (if s + 2 = L' + 1 ∧ l[s + 1]? = some e then 1 else 0) ≤ if s = L' - 1 then 1 else 0 := by
          intro s _
          split_ifs with h4 h5 h5
          · exact le_rfl
          · omega
          · exact Nat.zero_le _
          · exact le_rfl
        refine (Finset.sum_le_sum h3).trans ?_
        rw [Finset.sum_ite_eq']
        split_ifs <;> omega
    · rw [if_neg hc, Nat.le_zero, Nat.add_eq_zero_iff]
      constructor
      · refine Finset.sum_eq_zero fun s _ => if_neg ?_
        rintro ⟨h4, h5⟩
        have : s + 1 = L' := by omega
        rw [this] at h5
        exact hc h5
      · rw [if_neg]
        rintro ⟨h4, h5⟩
        have : L' = 0 := by omega
        rw [this] at hc
        exact hc h5

section

variable (hr : 0 < r) (hb : 0 < b)
include hr hb

/-- The load of an edge after the start. -/
theorem load_start_le (e : T.Ed 0) : load R ch FL lhat n o (.edge 0 e) ≤
    ∑ a, ∑ c, ∑ γ, if a = c then 0 else Bt T ch lhat n a c γ * (R.path (ch a) (ch c) γ).count e := by
  classical
  -- initial units
  have h1 : bt R ch lhat n (.edge 0 e : Tg T m AA) ≤ ∑ a, ∑ c, ∑ γ, if a = c then 0 else
      Bt T ch lhat n a c γ * if R.pl (ch a) (ch c) γ ≤ 1 ∧ (R.path (ch a) (ch c) γ)[0]? = some e then 1 else 0 := by
    unfold bt
    by_cases hv : Valid lhat n
    · rw [if_pos hv]
      refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun c _ => ?_
      by_cases hac : a = c
      · rw [card_eq_zero.2]
        · exact Nat.zero_le _
        · refine filter_false_of_mem fun k _ h3 => ?_
          rcases tgB_cases (R := R) (ch := ch) a c k with h1 | ⟨hm, h1⟩ | ⟨e', -, h1, h2, -⟩
          · rw [h1] at h3; simp at h3
          · rw [h1] at h3; simp at h3
          · exact h2 hac
      · simp only [if_neg hac]
        rw [card_eq_sum_card_fiberwise (f := fun k => gam T ch a k) (t := univ) (fun _ _ => mem_coe.2 (mem_univ _))]
        refine Finset.sum_le_sum fun γ _ => ?_
        by_cases hc : R.pl (ch a) (ch c) γ ≤ 1 ∧ (R.path (ch a) (ch c) γ)[0]? = some e
        · rw [if_pos hc, Nat.mul_one]
          unfold Bt
          rw [if_pos hv]
          refine card_le_card fun k hk => ?_
          obtain ⟨h2, h3⟩ := mem_filter.1 hk
          exact mem_filter.2 ⟨(mem_filter.1 h2).1, h3⟩
        · rw [if_neg hc, Nat.mul_zero, Nat.le_zero, card_eq_zero]
          refine filter_false_of_mem fun k hk h3 => hc ?_
          have h4 := (mem_filter.1 hk).2
          rcases tgB_cases (R := R) (ch := ch) a c k with h1 | ⟨hm, h1⟩ | ⟨e', h0, h1, h2, h5⟩ <;> rw [h1] at h4
          · simp at h4
          · simp at h4
          · have h6 : e' = e := eq_of_heq (Tg.edge.inj h4).2
            subst h6
            rw [h3] at h0 h5
            exact ⟨by omega, h0⟩
    · rw [if_neg hv]
      exact Nat.zero_le _
  -- relays
  have h2 : (∑ ν : NM R FL (ch := ch), if tgM R ch FL ν.1 ν.2 = .edge 0 e then alv R ch FL lhat n o ν else 0) ≤
      ∑ a, ∑ c, ∑ γ, ∑ s : Fin (2 * m), if a = c then 0 else Bt T ch lhat n a c γ *
        ((if s.1 + 1 < R.pl (ch a) (ch c) γ ∧ (R.path (ch a) (ch c) γ)[s.1]? = some e then 1 else 0) +
        if s.1 + 2 = R.pl (ch a) (ch c) γ ∧ (R.path (ch a) (ch c) γ)[s.1 + 1]? = some e then 1 else 0) := by
    -- only the relays of the start
    have h3 : ∀ ν : NM R FL (ch := ch), (if tgM R ch FL ν.1 ν.2 = .edge 0 e then alv R ch FL lhat n o ν else 0) ≤
        ∑ a, ∑ c, ∑ γ, ∑ s : Fin (2 * m), ((if ∃ hx : okR T R ch (.start a c γ s), ν = ⟨.inl ⟨.start a c γ s, hx⟩, false⟩ ∧
            (R.path (ch a) (ch c) γ)[s.1]? = some e then Bt T ch lhat n a c γ else 0) +
          if ∃ hx : okR T R ch (.start a c γ s), ν = ⟨.inl ⟨.start a c γ s, hx⟩, true⟩ ∧ s.1 + 2 = R.pl (ch a) (ch c) γ ∧
            (R.path (ch a) (ch c) γ)[s.1 + 1]? = some e then Bt T ch lhat n a c γ else 0) := by
      intro ν
      split_ifs with hν
      · rcases ν with ⟨⟨x, hx⟩ | l, ν⟩
        · change tgR T R ch x ν = .edge 0 e at hν
          have hnum := alv_le_num (lhat := lhat) (n := n) (o := o) (FL := FL) hr hb ⟨x, hx⟩ ν
          rcases x with ⟨a, c, γ, s⟩ | ⟨j', i', e'⟩ | ⟨j', e', s'⟩ | e'
          · have hB := hnum.trans (num_start_le (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb a c γ s hx)
            refine le_trans ?_ (Finset.single_le_sum (f := fun a => ∑ c, ∑ γ, ∑ s : Fin (2 * m), _)
              (fun _ _ => Nat.zero_le _) (mem_univ a))
            refine le_trans ?_ (Finset.single_le_sum (f := fun c => ∑ γ, ∑ s : Fin (2 * m), _)
              (fun _ _ => Nat.zero_le _) (mem_univ c))
            refine le_trans ?_ (Finset.single_le_sum (f := fun γ => ∑ s : Fin (2 * m), _)
              (fun _ _ => Nat.zero_le _) (mem_univ γ))
            refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ s))
            have hedge : ∀ e' : Option (T.Ed 0), (edgeO T e' : Tg T m AA) = .edge 0 e → e' = some e := by
              intro e' he
              cases e' with
              | none => simp [edgeO] at he
              | some e'' =>
                have h6 : e'' = e := eq_of_heq (Tg.edge.inj he).2
                rw [h6]
            cases ν
            · rw [if_pos ⟨hx, rfl, hedge _ hν⟩]
              exact hB.trans (Nat.le_add_right _ _)
            · simp only [tgR] at hν
              split_ifs at hν with hs
              have h4 : s.1 + 2 = R.pl (ch a) (ch c) γ := by
                obtain ⟨-, h5⟩ := hx
                have h6 := (R.pl_le (ch a) (ch c) γ).trans (R.length_path _ _ _)
                by_contra h7
                exact hs ⟨by omega, by omega⟩
              rw [if_pos (⟨hx, rfl, h4, hedge _ hν⟩ : ∃ hx : okR T R ch (.start a c γ s),
                (⟨.inl ⟨.start a c γ s, _⟩, true⟩ : NM R FL (ch := ch)) = ⟨.inl ⟨.start a c γ s, hx⟩, true⟩ ∧ s.1 + 2 = R.pl (ch a) (ch c) γ ∧
                (R.path (ch a) (ch c) γ)[s.1 + 1]? = some e)]
              exact hB.trans (Nat.le_add_left _ _)
          · simp [tgR] at hν
          · exfalso
            cases ν
            · fin_cases s'
              · simp [tgR] at hν
              · simp [tgR] at hν
              · exact absurd (Tg.edge.inj hν).1 (Fin.succ_ne_zero _)
              · simp [tgR] at hν
            · fin_cases s'
              · simp only [tgR, Fin.zero_eta, Matrix.cons_val_zero] at hν
                split_ifs at hν
              · simp [tgR] at hν
              · simp only [tgR, Fin.reduceFinMk, Matrix.cons_val] at hν
                split_ifs at hν
              · simp [tgR] at hν
          · simp [tgR] at hν
        · exfalso
          exact absurd (Tg.edge.inj hν).1 (Fin.succ_ne_zero _)
      · exact Nat.zero_le _
    refine (Finset.sum_le_sum fun ν _ => h3 ν).trans ?_
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun c _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun γ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [Finset.sum_add_distrib]
    have sgl : ∀ (d : Bool) (P : Prop) [Decidable P] (v : ℕ), (∑ ν : NM R FL (ch := ch), if ∃ hx : okR T R ch (.start a c γ s),
        ν = ⟨.inl ⟨.start a c γ s, hx⟩, d⟩ ∧ P then v else 0) ≤
          if okR T R ch (.start a c γ s) ∧ P then v else 0 := by
      intro d P _ v
      by_cases hc : okR T R ch (.start a c γ s) ∧ P
      · rw [if_pos hc, Finset.sum_eq_single (⟨.inl ⟨.start a c γ s, hc.1⟩, d⟩ : NM R FL (ch := ch))]
        · rw [if_pos ⟨hc.1, rfl, hc.2⟩]
        · intro ν _ hν
          rw [if_neg]
          rintro ⟨hx', h3, -⟩
          exact hν h3
        · intro hn; exact absurd (mem_univ _) hn
      · rw [Finset.sum_eq_zero]
        · exact Nat.zero_le _
        · intro ν _
          rw [if_neg]
          rintro ⟨hx, -, h1⟩
          exact hc ⟨hx, h1⟩
    refine (add_le_add (sgl false _ _) (sgl true _ _)).trans ?_
    by_cases hac : a = c
    · rw [if_pos hac, if_neg (fun hh => hh.1.1 hac), if_neg (fun hh => hh.1.1 hac)]
    · rw [if_neg hac, Nat.mul_add]
      refine add_le_add ?_ ?_
      · split_ifs with h4 h5 h5
        · rw [Nat.mul_one]
        · exact absurd ⟨h4.1.2, h4.2⟩ h5
        · exact Nat.zero_le _
        · exact Nat.zero_le _
      · split_ifs with h4 h5 h5
        · rw [Nat.mul_one]
        · exact absurd h4.2 h5
        · exact Nat.zero_le _
        · exact Nat.zero_le _
  rw [load_def]
  refine (add_le_add h1 h2).trans ?_
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun γ _ => ?_
  by_cases hac : a = c
  · simp [hac]
  · simp only [if_neg hac]
    rw [← Finset.mul_sum, ← Nat.mul_add]
    refine Nat.mul_le_mul_left _ ?_
    have hne : ch a ≠ ch c := fun hh => hac (ch.injective hh)
    have := steps_le (R.path (ch a) (ch c) γ) e (R.pl (ch a) (ch c) γ) (2 * m) (R.pl_pos hne γ) (R.pl_le _ _ _)
    rw [Finset.sum_range] at this
    rw [Nat.add_comm]
    exact this

omit hr hb in
/-- The batches on an edge. -/
theorem batch_le (e : T.Ed 0) : (∑ a, ∑ c, ∑ γ, if a = c then 0 else
    Bt T ch lhat n a c γ * (R.path (ch a) (ch c) γ).count e) ≤ Uu * (lhat / Fintype.card (T.X 0) + 2 * AA) := by
  classical
  by_cases hv : Valid lhat n
  swap
  · refine le_trans (le_of_eq ?_) (Nat.zero_le _)
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun γ _ => ?_
    unfold Bt
    rw [if_neg hv]
    simp
  -- split the paths
  set cn : Fin AA → T.X 0 → ℕ := fun a γ => (R.rt (ch a) γ).count e with hcn
  have e1 : ∀ a c γ, (if a = c then 0 else Bt T ch lhat n a c γ * (R.path (ch a) (ch c) γ).count e) =
      (if a = c then 0 else Bt T ch lhat n a c γ * cn a γ) + if a = c then 0 else Bt T ch lhat n a c γ * cn c γ := by
    intro a c γ
    split_ifs
    · rfl
    · rw [Routes.path, List.count_append, List.count_reverse, Nat.mul_add]
  have e2 : (∑ a, ∑ c, ∑ γ, if a = c then 0 else Bt T ch lhat n a c γ * cn c γ) =
      ∑ a, ∑ c, ∑ γ, if a = c then 0 else Bt T ch lhat n c a γ * cn a γ := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun γ _ => ?_
    exact if_congr eq_comm rfl rfl
  have e3 : (∑ a, ∑ c, ∑ γ, if a = c then 0 else Bt T ch lhat n a c γ * (R.path (ch a) (ch c) γ).count e) =
      ∑ a, ∑ γ, cn a γ * ∑ c, if c = a then 0 else Bt T ch lhat n a c γ + Bt T ch lhat n c a γ := by
    simp only [e1, Finset.sum_add_distrib]
    rw [e2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    have : ∀ c, (∑ γ, if a = c then 0 else Bt T ch lhat n a c γ * cn a γ) + (∑ γ, if a = c then 0 else Bt T ch lhat n c a γ * cn a γ) =
        ∑ γ, if a = c then 0 else cn a γ * (Bt T ch lhat n a c γ + Bt T ch lhat n c a γ) := by
      intro c
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun γ _ => ?_
      split_ifs
      · rfl
      · ring
    rw [Finset.sum_congr rfl fun c _ => this c, Finset.sum_comm]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hac : a = c
    · simp [hac]
    · rw [if_neg hac, if_neg (Ne.symm hac)]
  rw [e3]
  have hB : ∀ a γ, (∑ c, if c = a then 0 else Bt T ch lhat n a c γ + Bt T ch lhat n c a γ) ≤
      lhat / Fintype.card (T.X 0) + 2 * AA := by
    intro a γ
    have hX : 0 < Fintype.card (T.X 0) := Fintype.card_pos_iff.2 ⟨ch a⟩
    have h1 : (∑ c, if c = a then 0 else Bt T ch lhat n a c γ + Bt T ch lhat n c a γ) ≤
        ∑ c, ((if c = a then 0 else n a c / Fintype.card (T.X 0) + n c a / Fintype.card (T.X 0)) + 2) := by
      refine Finset.sum_le_sum fun c _ => ?_
      split_ifs
      · exact Nat.zero_le _
      · have := Bt_le (ch := ch) (lhat := lhat) (n := n) a c γ
        have := Bt_le (ch := ch) (lhat := lhat) (n := n) c a γ
        omega
    refine h1.trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_comm AA 2]
    refine Nat.add_le_add_right ?_ _
    rw [Nat.le_div_iff_mul_le hX, Finset.sum_mul]
    refine le_trans (Finset.sum_le_sum fun c _ => ?_) (hv a)
    split_ifs
    · simp
    · rw [Nat.add_mul]
      exact add_le_add (Nat.div_mul_le_self _ _) (Nat.div_mul_le_self _ _)
  calc ∑ a, ∑ γ, cn a γ * _ ≤ ∑ a, ∑ γ, cn a γ * (lhat / Fintype.card (T.X 0) + 2 * AA) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun γ _ => Nat.mul_le_mul_left _ (hB a γ)
    _ = (∑ a, ∑ γ, cn a γ) * (lhat / Fintype.card (T.X 0) + 2 * AA) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_mul]
    _ ≤ _ := by
        refine Nat.mul_le_mul_right _ ?_
        refine le_trans ?_ (R.use e)
        calc ∑ a, ∑ γ, cn a γ = ∑ c ∈ univ.map ch, ∑ γ, (R.rt c γ).count e := by rw [Finset.sum_map]
          _ ≤ _ := Finset.sum_le_sum_of_subset (subset_univ _)

/-- **Paper: Theorem thm:tree, Start.** "Every edge gets at most n₀ = 4L(N+M²) units": every edge of X^(0) gets at
most Uu (N/|X^(0)| + 2AA), where Uu ≤ 2|X^(0)|L bounds the routes through an edge (printed form: thm_tree_start_units). -/
theorem _root_.Paper.thm_tree_start (e : T.Ed 0) : load R ch FL lhat n o (.edge 0 e) ≤
    Uu * (lhat / Fintype.card (T.X 0) + 2 * AA) := (load_start_le hr hb e).trans (batch_le e)

end

end Nc.Tow
