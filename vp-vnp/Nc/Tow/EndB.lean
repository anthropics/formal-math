/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.EndA

/-!
# The tower plan: units between a node and its parent
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b D J r m Uu AA : ℕ} {T : Tower h b D J r} {R : Routes T m Uu}
  {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {lhat : ℕ} {n : Fin AA → Fin AA → ℕ} {o : NM R FL (ch := ch) → ℕ}

/-- The parent of a chamber, as a node. -/
noncomputable def parN (hh : 0 < h) (Lf : ∀ j, T.Ed j → ℕ) (j : ℕ) (c : T.X j) : Nd T :=
  if hj : j + 1 ≤ J then nd T (j + 1) hj (hostj hh Lf c) else none

/-- The chamber below: which end of the edge of a relay. -/
def chd : RM T m AA → Bool → Option (Σ j : Fin (J + 1), T.X j)
  | .inn j _ e, β => some ⟨j.castSucc, if β then T.e1 e else T.e0 e⟩
  | .mid j e _, β => some ⟨j.castSucc, if β then T.e1 e else T.e0 e⟩
  | .fin e, β => some ⟨Fin.last J, if β then T.e1 e else T.e0 e⟩
  | _, _ => none

variable (hr : 0 < r) (hb : 0 < b) (hh : 0 < h)
include hr hb hh

theorem num_inn (j : Fin J) (i : Fin h) (e : T.Ed j) (hx : okR T R ch (.inn j i e)) (hne : num R ch FL lhat n o (.inl ⟨.inn j i e, hx⟩) ≠ 0) :
    i = imin hh (lev (load R ch FL lhat n o)) j.1 := by
  classical
  rw [num_eq hr hb, numF] at hne
  split_ifs at hne with ha
  · exact (isMin_iff hh _ j.castSucc i).1 ha
  · exact absurd rfl hne

theorem num_mid (j : Fin J) (e : T.Ed j) (s : Fin 4) (hx : okR T R ch (.mid j e s))
    (hne : num R ch FL lhat n o (.inl ⟨.mid j e s, hx⟩) ≠ 0) :
    T.ty e = imin hh (lev (load R ch FL lhat n o)) j.1 := by
  obtain ⟨hx0, h1⟩ := num_mid_le (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb j e s hx
  have h2 := (num_mid0 (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb j e hx0).2
  by_contra hcon
  have h3 : ¬ IsMin (load R ch FL lhat n o) j.castSucc (T.ty e) := fun hm => hcon ((isMin_iff hh _ j.castSucc _).1 hm)
  have := h2 h3
  omega

/-- A chamber and its parent hold the units of a channel without target. -/
theorem done_hold {x : RM T m AA} (hx : okR T R ch x) {β : Bool} (hd : tgR T R ch x β = .done)
    (hne : num R ch FL lhat n o (.inl ⟨x, hx⟩) ≠ 0) :
    ∃ (j : ℕ) (hj : j ≤ J) (c : T.X j), chd x β = some ⟨⟨j, Nat.lt_succ_of_le hj⟩, c⟩ ∧
      hN (⟨.inl ⟨x, hx⟩, β⟩ : NM R FL (ch := ch)) =
        s(nd T j hj c, parN hh (lev (load R ch FL lhat n o)) j c) := by
  have e0 : ∀ β : Bool, hN (⟨.inl ⟨x, hx⟩, β⟩ : NM R FL (ch := ch)) =
      if β then s(tri T R ch x 1, tri T R ch x 2) else s(tri T R ch x 0, tri T R ch x 1) := by
    intro β
    cases β <;> rfl
  rw [e0]
  rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e
  · exfalso
    obtain ⟨hac, hs⟩ := hx
    cases β
    · simp only [tgR] at hd
      exact (edgeO_hold (R := R) (ch := ch) (AA := AA) (m := m) (c := ch a) (c' := ch c) (γ := γ) (s := s.1) (by omega)).1 hd
    · simp only [tgR] at hd
      split_ifs at hd
      exact (edgeO_hold (R := R) (ch := ch) (AA := AA) (m := m) (c := ch a) (c' := ch c) (γ := γ) (s := s.1 + 1) hs).1 hd
  · have hi := num_inn hr hb hh j i e hx hne
    have hjJ := j.2
    have hpar : ∀ c : T.X j.1, parN hh (lev (load R ch FL lhat n o)) j.1 c = nd T (j + 1) j.2 (hst T i c) := by
      intro c
      unfold parN
      rw [dif_pos (by omega : j.1 + 1 ≤ J), hi]
      rfl
    cases β
    · refine ⟨j.1, j.2.le, T.e0 e, rfl, ?_⟩
      rw [hpar]
      rfl
    · refine ⟨j.1, j.2.le, T.e1 e, rfl, ?_⟩
      rw [hpar]
      have h1 : T.vx i (T.e0 e) = T.vx i (T.e1 e) := by
        rw [T.nr_vx0 j.2.le i ⟨e, hx⟩, T.nr_vx1 j.2.le i ⟨e, hx⟩]
      have h2 : hst T i (T.e0 e) = hst T i (T.e1 e) := by
        unfold hst
        rw [h1]
      change s(nd T (j + 1) j.2 (hst T i (T.e0 e)), nd T j j.2.le (T.e1 e)) = _
      rw [h2, Sym2.eq_swap]
  · have hi := num_mid hr hb hh j e s hx hne
    have hjJ := j.2
    have hpar : ∀ c : T.X j.1, parN hh (lev (load R ch FL lhat n o)) j.1 c = nd T (j + 1) j.2 (hst T (T.ty e) c) := by
      intro c
      unfold parN
      rw [dif_pos (by omega : j.1 + 1 ≤ J), hi]
      rfl
    cases β
    · refine ⟨j.1, j.2.le, T.e0 e, rfl, ?_⟩
      rw [hpar]
      fin_cases s
      · rfl
      · simp [tgR] at hd
      · simp [tgR] at hd
      · simp [tgR] at hd
    · refine ⟨j.1, j.2.le, T.e1 e, rfl, ?_⟩
      rw [hpar]
      fin_cases s
      · simp only [tgR, Fin.zero_eta, Matrix.cons_val_zero] at hd
        split_ifs at hd
      · simp [tgR] at hd
      · simp only [tgR, Fin.reduceFinMk, Matrix.cons_val] at hd
        split_ifs at hd with hq
        rw [not_not] at hq
        change s(nd T (j + 1) j.2 (T.π (T.e1 e)), nd T j j.2.le (T.e1 e)) = _
        rw [hq, Sym2.eq_swap]
      · change s(nd T (j + 1) j.2 (hst T (T.ty e) (T.e1 e)), nd T j j.2.le (T.e1 e)) = _
        rw [Sym2.eq_swap]
  · have hpar : ∀ c : T.X J, parN hh (lev (load R ch FL lhat n o)) J c = none := by
      intro c
      unfold parN
      rw [dif_neg (by omega)]
    cases β
    · refine ⟨J, le_rfl, T.e0 e, rfl, ?_⟩
      rw [hpar]
      rfl
    · refine ⟨J, le_rfl, T.e1 e, rfl, ?_⟩
      rw [hpar]
      change s(none, nd T J le_rfl (T.e1 e)) = _
      rw [Sym2.eq_swap]

omit hr hb hh in
/-- A sum over at most one element. -/
theorem sum_le_one {κ : Type*} (s : Finset κ) (f : κ → ℕ) (B : ℕ) (h1 : ∀ x ∈ s, ∀ y ∈ s, x = y) (h2 : ∀ x ∈ s, f x ≤ B) :
    ∑ x ∈ s, f x ≤ B := by
  rcases s.eq_empty_or_nonempty with h0 | ⟨x, hx⟩
  · rw [h0, Finset.sum_empty]; exact Nat.zero_le _
  · have : s = {x} := by
      ext y
      rw [mem_singleton]
      exact ⟨fun hy => h1 y hy x hx, fun hy => hy ▸ hx⟩
    rw [this, Finset.sum_singleton]
    exact h2 x hx

/-- The channel is between the chamber `s` and its parent. -/
def IsCh (R : Routes T m Uu) (ch : Fin AA ↪ T.X 0) (FL : FlagLaws F T) (ν : NM R FL (ch := ch)) (s : Σ j : Fin (J + 1), T.X j) : Prop :=
  ∃ (x : {x : RM T m AA // okR T R ch x}) (β : Bool), ν = ⟨.inl x, β⟩ ∧ tgR T R ch x.1 β = .done ∧ chd x.1 β = some s

/-- The relay belongs to an edge. -/
def OfEd (j : Fin J) (e : T.Ed j) (x : RM T m AA) : Prop := (∃ i, x = .inn j i e) ∨ ∃ s, x = .mid j e s

/-- At most one channel of an edge and an end has alive units. -/
theorem ofEd_unique {j : Fin J} {e : T.Ed j} {β : Bool} {x x' : RM T m AA} (hx : okR T R ch x) (hx' : okR T R ch x')
    (h1 : OfEd j e x) (h1' : OfEd j e x') (hd : tgR T R ch x β = .done) (hd' : tgR T R ch x' β = .done)
    (hn : num R ch FL lhat n o (.inl ⟨x, hx⟩) ≠ 0) (hn' : num R ch FL lhat n o (.inl ⟨x', hx'⟩) ≠ 0) : x = x' := by
  have mm : ∀ s s' : Fin 4, okR T R ch (.mid j e s) → okR T R ch (.mid j e s') → tgR T R ch (.mid j e s : RM T m AA) β = .done →
      tgR T R ch (.mid j e s' : RM T m AA) β = .done → s = s' := by
    intro s s' hs hs' h2 h2'
    cases β
    · have h0 : ∀ s : Fin 4, tgR T R ch (.mid j e s : RM T m AA) false = .done → s = 0 := by
        intro s hs
        fin_cases s
        · rfl
        · simp [tgR] at hs
        · simp [tgR] at hs
        · simp [tgR] at hs
      rw [h0 s h2, h0 s' h2']
    · have h0 : ∀ s : Fin 4, tgR T R ch (.mid j e s : RM T m AA) true = .done → okR T R ch (.mid j e s) →
          (s = 2 ∧ T.π (T.e1 e) = hst T (T.ty e) (T.e1 e)) ∨ (s = 3 ∧ T.π (T.e1 e) ≠ hst T (T.ty e) (T.e1 e)) := by
        intro s hs hok
        fin_cases s
        · exfalso
          simp only [tgR, Fin.zero_eta, Matrix.cons_val_zero] at hs
          split_ifs at hs
        · simp [tgR] at hs
        · left
          simp only [tgR, Fin.reduceFinMk, Matrix.cons_val] at hs
          split_ifs at hs with hq
          exact ⟨rfl, not_not.1 hq⟩
        · exact Or.inr ⟨rfl, hok.2 rfl⟩
      rcases h0 s h2 hs with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases h0 s' h2' hs' with ⟨b1, b2⟩ | ⟨b1, b2⟩
      · rw [a1, b1]
      · exact absurd a2 b2
      · exact absurd b2 a2
      · rw [a1, b1]
  rcases h1 with ⟨i, rfl⟩ | ⟨s, rfl⟩ <;> rcases h1' with ⟨i', rfl⟩ | ⟨s', rfl⟩
  · rw [num_inn hr hb hh j i e hx hn, num_inn hr hb hh j i' e hx' hn']
  · exfalso
    have a1 := num_inn hr hb hh j i e hx hn
    have a2 := num_mid hr hb hh j e s' hx' hn'
    exact hx (a2.trans a1.symm)
  · exfalso
    have a1 := num_inn hr hb hh j i' e hx' hn'
    have a2 := num_mid hr hb hh j e s hx hn
    exact hx' (a2.trans a1.symm)
  · rw [mm s s' hx hx' hd hd']

open Classical in
/-- The alive units of an edge at one end. -/
theorem sum_edge_end (j : Fin J) (e : T.Ed j) (β : Bool) : ∑ ν ∈ (univ : Finset (NM R FL (ch := ch))).filter (fun ν =>
      alv R ch FL lhat n o ν ≠ 0 ∧ ∃ x : {x : RM T m AA // okR T R ch x}, ν = ⟨.inl x, β⟩ ∧ tgR T R ch x.1 β = .done ∧ OfEd j e x.1),
      alv R ch FL lhat n o ν ≤ load R ch FL lhat n o (.edge j.castSucc e) := by
  have hnz : ∀ (x : {x : RM T m AA // okR T R ch x}), alv R ch FL lhat n o (⟨.inl x, β⟩ : NM R FL (ch := ch)) ≠ 0 →
      num R ch FL lhat n o (.inl x) ≠ 0 := by
    intro x hx
    have := alv_le_num (lhat := lhat) (n := n) (o := o) (FL := FL) hr hb x β
    omega
  refine sum_le_one _ _ _ ?_ ?_
  · intro ν hν ν' hν'
    obtain ⟨-, h0, ⟨x, hx⟩, rfl, h2, h3⟩ := mem_filter.1 hν
    obtain ⟨-, h0', ⟨x', hx'⟩, rfl, h2', h3'⟩ := mem_filter.1 hν'
    have : x = x' := ofEd_unique hr hb hh hx hx' h3 h3' h2 h2' (hnz _ h0) (hnz _ h0')
    subst this
    rfl
  · intro ν hν
    obtain ⟨-, h0, ⟨x, hx⟩, rfl, h2, h3⟩ := mem_filter.1 hν
    rcases h3 with ⟨i, h3⟩ | ⟨s, h3⟩
    · simp only at h3
      subst h3
      exact (alv_le_num hr hb _ _).trans (num_inl hr hb _)
    · simp only at h3
      subst h3
      exact (alv_mid_le hr hb j e s hx β).1

open Classical in
/-- The alive units between a chamber of a level before the last and its parent. -/
theorem sum_child_lt (j : Fin J) (c : T.X j) : (∑ ν : NM R FL (ch := ch), if IsCh R ch FL ν ⟨j.castSucc, c⟩ then
      alv R ch FL lhat n o ν else 0) ≤
    ∑ e : T.Ed j, if T.e0 e = c ∨ T.e1 e = c then load R ch FL lhat n o (.edge j.castSucc e) else 0 := by
  let C : T.Ed j → Bool → Finset (NM R FL (ch := ch)) := fun e β => (univ : Finset (NM R FL (ch := ch))).filter (fun ν =>
      alv R ch FL lhat n o ν ≠ 0 ∧ ∃ x : {x : RM T m AA // okR T R ch x}, ν = ⟨.inl x, β⟩ ∧ tgR T R ch x.1 β = .done ∧ OfEd j e x.1)
  have hall : ∀ ν : NM R FL (ch := ch), (if IsCh R ch FL ν ⟨j.castSucc, c⟩ then alv R ch FL lhat n o ν else 0) ≤
      if ν ∈ ((univ.filter fun e : T.Ed j => T.e0 e = c).biUnion fun e => C e false) ∪
        ((univ.filter fun e : T.Ed j => T.e1 e = c).biUnion fun e => C e true) then alv R ch FL lhat n o ν else 0 := by
    intro ν
    by_cases h1 : IsCh R ch FL ν ⟨j.castSucc, c⟩
    swap
    · rw [if_neg h1]; exact Nat.zero_le _
    rw [if_pos h1]
    by_cases h0 : alv R ch FL lhat n o ν = 0
    · rw [h0]; exact Nat.zero_le _
    rw [if_pos]
    obtain ⟨x, β, hν, hd, hc⟩ := h1
    have hmem : ∀ e, OfEd j e x.1 → ν ∈ C e β := fun e he => mem_filter.2 ⟨mem_univ _, h0, x, hν, hd, he⟩
    have hex : ∃ e : T.Ed j, OfEd j e x.1 ∧ (if β then T.e1 e else T.e0 e) = c := by
      obtain ⟨x, hx⟩ := x
      simp only at hc ⊢
      rcases x with ⟨a, c', γ, s⟩ | ⟨j', i, e⟩ | ⟨j', e, s⟩ | e
      · simp [chd] at hc
      · simp only [chd, Option.some.injEq, Sigma.mk.injEq] at hc
        obtain ⟨hj, hc⟩ := hc
        have hj : j' = j := Fin.castSucc_injective _ hj
        subst hj
        exact ⟨e, Or.inl ⟨i, rfl⟩, eq_of_heq hc⟩
      · simp only [chd, Option.some.injEq, Sigma.mk.injEq] at hc
        obtain ⟨hj, hc⟩ := hc
        have hj : j' = j := Fin.castSucc_injective _ hj
        subst hj
        exact ⟨e, Or.inr ⟨s, rfl⟩, eq_of_heq hc⟩
      · simp only [chd, Option.some.injEq, Sigma.mk.injEq] at hc
        exact absurd hc.1.symm (Fin.castSucc_lt_last j).ne
    obtain ⟨e, he, hce⟩ := hex
    cases β
    · exact mem_union_left _ (mem_biUnion.2 ⟨e, mem_filter.2 ⟨mem_univ _, by simpa using hce⟩, hmem e he⟩)
    · exact mem_union_right _ (mem_biUnion.2 ⟨e, mem_filter.2 ⟨mem_univ _, by simpa using hce⟩, hmem e he⟩)
  refine (Finset.sum_le_sum fun ν _ => hall ν).trans ?_
  rw [← Finset.sum_filter, filter_mem_eq_inter, univ_inter]
  refine (sum_union_le _ _ _).trans ?_
  refine (add_le_add (sum_biUnion_le' _ _ _) (sum_biUnion_le' _ _ _)).trans ?_
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun e _ => ?_
  have hne := T.e_ne e
  by_cases h0 : T.e0 e = c
  · have h1 : ¬ T.e1 e = c := fun hcon => hne (h0.trans hcon.symm)
    rw [if_pos h0, if_neg h1, if_pos (Or.inl h0)]
    exact sum_edge_end hr hb hh j e false
  · by_cases h1 : T.e1 e = c
    · rw [if_neg h0, if_pos h1, if_pos (Or.inr h1), Nat.zero_add]
      exact sum_edge_end hr hb hh j e true
    · rw [if_neg h0, if_neg h1]
      exact Nat.zero_le _

open Classical in
/-- The alive units between a chamber of the last level and the root. -/
theorem sum_child_last (c : T.X J) : (∑ ν : NM R FL (ch := ch), if IsCh R ch FL ν ⟨Fin.last J, c⟩ then
      alv R ch FL lhat n o ν else 0) ≤
    ∑ e : T.Ed J, if T.e0 e = c ∨ T.e1 e = c then load R ch FL lhat n o (.edge (Fin.last J) e) else 0 := by
  let C : T.Ed J → Bool → Finset (NM R FL (ch := ch)) := fun e β => {⟨.inl ⟨.fin e, trivial⟩, β⟩}
  have hC : ∀ e β, ∑ ν ∈ C e β, alv R ch FL lhat n o ν ≤ load R ch FL lhat n o (.edge (Fin.last J) e) := by
    intro e β
    simp only [C]
    rw [Finset.sum_singleton]
    exact (alv_le_num hr hb _ _).trans (num_inl hr hb _)
  have hall : ∀ ν : NM R FL (ch := ch), (if IsCh R ch FL ν ⟨Fin.last J, c⟩ then alv R ch FL lhat n o ν else 0) ≤
      if ν ∈ ((univ.filter fun e : T.Ed J => T.e0 e = c).biUnion fun e => C e false) ∪
        ((univ.filter fun e : T.Ed J => T.e1 e = c).biUnion fun e => C e true) then alv R ch FL lhat n o ν else 0 := by
    intro ν
    by_cases h1 : IsCh R ch FL ν ⟨Fin.last J, c⟩
    swap
    · rw [if_neg h1]; exact Nat.zero_le _
    rw [if_pos h1, if_pos]
    obtain ⟨⟨x, hx⟩, β, hν, hd, hc⟩ := h1
    rcases x with ⟨a, c', γ, s⟩ | ⟨j', i, e⟩ | ⟨j', e, s⟩ | e
    · simp [chd] at hc
    · simp only [chd, Option.some.injEq, Sigma.mk.injEq] at hc
      exact absurd hc.1 (Fin.castSucc_lt_last j').ne
    · simp only [chd, Option.some.injEq, Sigma.mk.injEq] at hc
      exact absurd hc.1 (Fin.castSucc_lt_last j').ne
    · simp only [chd, Option.some.injEq, Sigma.mk.injEq] at hc
      have hce : (if β then T.e1 e else T.e0 e) = c := eq_of_heq hc.2
      have hmem : ν ∈ C e β := by
        rw [hν]
        exact mem_singleton_self _
      cases β
      · exact mem_union_left _ (mem_biUnion.2 ⟨e, mem_filter.2 ⟨mem_univ _, by simpa using hce⟩, hmem⟩)
      · exact mem_union_right _ (mem_biUnion.2 ⟨e, mem_filter.2 ⟨mem_univ _, by simpa using hce⟩, hmem⟩)
  refine (Finset.sum_le_sum fun ν _ => hall ν).trans ?_
  rw [← Finset.sum_filter, filter_mem_eq_inter, univ_inter]
  refine (sum_union_le _ _ _).trans ?_
  refine (add_le_add (sum_biUnion_le' _ _ _) (sum_biUnion_le' _ _ _)).trans ?_
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun e _ => ?_
  have hne := T.e_ne e
  by_cases h0 : T.e0 e = c
  · have h1 : ¬ T.e1 e = c := fun hcon => hne (h0.trans hcon.symm)
    rw [if_pos h0, if_neg h1, if_pos (Or.inl h0)]
    exact hC e false
  · by_cases h1 : T.e1 e = c
    · rw [if_neg h0, if_pos h1, if_pos (Or.inr h1), Nat.zero_add]
      exact hC e true
    · rw [if_neg h0, if_neg h1]
      exact Nat.zero_le _

open Classical in
/-- **The alive units between a chamber and its parent.** -/
theorem sum_child (j : ℕ) (hj : j ≤ J) (c : T.X j) : (∑ ν : NM R FL (ch := ch),
      if IsCh R ch FL ν ⟨⟨j, Nat.lt_succ_of_le hj⟩, c⟩ then alv R ch FL lhat n o ν else 0) ≤
    fb (lev (load R ch FL lhat n o)) j c := by
  have e1 : fb (lev (load R ch FL lhat n o)) j c = ∑ e : T.Ed j, if T.e0 e = c ∨ T.e1 e = c then
      load R ch FL lhat n o (.edge ⟨j, Nat.lt_succ_of_le hj⟩ e) else 0 := by
    unfold fb Tower.bet lev
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [dif_pos (Nat.lt_succ_of_le hj)]
  rw [e1]
  rcases hj.lt_or_eq with h1 | h1
  · exact sum_child_lt hr hb hh ⟨j, h1⟩ c
  · subst h1
    exact sum_child_last hr hb hh c

end Nc.Tow
