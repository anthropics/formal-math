/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Flow

/-!
# The tower plan: loads of a stage
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b D J r m Uu AA : ℕ} {T : Tower h b D J r} {R : Routes T m Uu}
  {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {lhat : ℕ} {n : Fin AA → Fin AA → ℕ}
  {o : NM R FL (ch := ch) → ℕ}

theorem alv_le_num (hr : 0 < r) (hb : 0 < b) (x : {x : RM T m AA // okR T R ch x}) (ν : (kindM R ch FL (.inl x)).Cn) :
    alv R ch FL lhat n o ⟨.inl x, ν⟩ ≤ num R ch FL lhat n o (.inl x) := by
  unfold alv
  rw [alvN_inl]
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _

theorem load_def (τ : Tg T m AA) : load R ch FL lhat n o τ = bt R ch lhat n τ +
    ∑ ν : NM R FL (ch := ch), if tgM R ch FL ν.1 ν.2 = τ then alv R ch FL lhat n o ν else 0 := rfl

/-- A load that comes from few channels. -/
theorem load_le_sum {τ : Tg T m AA} (s : Finset (NM R FL (ch := ch))) (hbt : bt R ch lhat n τ = 0)
    (hs : ∀ ν : NM R FL (ch := ch), tgM R ch FL ν.1 ν.2 = τ → alv R ch FL lhat n o ν ≠ 0 → ν ∈ s) :
    load R ch FL lhat n o τ ≤ ∑ ν ∈ s, alv R ch FL lhat n o ν := by
  rw [load_def, hbt, Nat.zero_add, ← Finset.sum_filter]
  rw [← Finset.sum_filter_ne_zero]
  refine Finset.sum_le_sum_of_subset ?_
  intro ν hν
  obtain ⟨h1, h2⟩ := mem_filter.1 hν
  exact hs ν (mem_filter.1 h1).2 h2

theorem edgeO_cases (e : Option (T.Ed 0)) : (edgeO T e : Tg T m AA) = .done ∨ ∃ e', e = some e' ∧
    (edgeO T e : Tg T m AA) = .edge 0 e' := by
  cases e
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl, rfl⟩

/-- Targets of initial units. -/
theorem tgB_cases (a c : Fin AA) (k : ℕ) : (tgB T R ch a c k = .done) ∨
    (∃ hm, tgB T R ch a c k = .nxt (.start a c (gam T ch a k) ⟨0, hm⟩)) ∨
    ∃ e, (R.path (ch a) (ch c) (gam T ch a k))[0]? = some e ∧ tgB T R ch a c k = .edge 0 e ∧ a ≠ c ∧
      ¬ 1 < R.pl (ch a) (ch c) (gam T ch a k) := by
  have hle := (R.pl_le (ch a) (ch c) (gam T ch a k)).trans (R.length_path (ch a) (ch c) (gam T ch a k))
  unfold tgB
  by_cases hac : a = c
  · rw [if_pos hac]; exact Or.inl rfl
  · rw [if_neg hac]
    by_cases hs : 0 < 2 * m ∧ 1 < R.pl (ch a) (ch c) (gam T ch a k)
    · rw [dif_pos hs]; exact Or.inr (Or.inl ⟨hs.1, rfl⟩)
    · rw [dif_neg hs]
      rcases edgeO_cases (m := m) (AA := AA) ((R.path (ch a) (ch c) (gam T ch a k))[0]?) with h1 | ⟨e, h1, h2⟩
      · exact Or.inl h1
      · exact Or.inr (Or.inr ⟨e, h1, h2, hac, fun hh => hs ⟨by omega, hh⟩⟩)

theorem bt_zero {τ : Tg T m AA} (hτ : ∀ a c k, tgB T R ch a c k ≠ τ) : bt R ch lhat n τ = 0 := by
  unfold bt
  split_ifs
  · refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun c _ => ?_
    rw [card_eq_zero]
    exact filter_false_of_mem fun k _ => hτ a c k
  · rfl

theorem bt_edge_succ (j : Fin J) (e : T.Ed (j + 1)) : bt R ch lhat n (.edge j.succ e) = 0 := by
  refine bt_zero fun a c k hk => ?_
  rcases tgB_cases (R := R) (ch := ch) a c k with h1 | ⟨hm, h1⟩ | ⟨e', -, h1, -⟩ <;> rw [h1] at hk
  · simp at hk
  · simp at hk
  · exact absurd (Tg.edge.inj hk).1.symm (Fin.succ_ne_zero j)

theorem bt_seg (j : Fin J) (i : Fin h) (ω : T.V (j + 1) i) (q : Sym2 T.Fl) :
    bt R ch lhat n (.seg j i ω q : Tg T m AA) = 0 := by
  refine bt_zero fun a c k hk => ?_
  rcases tgB_cases (R := R) (ch := ch) a c k with h1 | ⟨hm, h1⟩ | ⟨e', -, h1, -⟩ <;> rw [h1] at hk <;> simp at hk

theorem bt_mid (j : Fin J) (e : T.Ed j) (s : Fin 4) : bt R ch lhat n (.nxt (.mid j e s) : Tg T m AA) = 0 := by
  refine bt_zero fun a c k hk => ?_
  rcases tgB_cases (R := R) (ch := ch) a c k with h1 | ⟨hm, h1⟩ | ⟨e', -, h1, -⟩ <;> rw [h1] at hk <;> simp at hk

section Targets

/-- Which channels of relays have a target of a given kind. -/
theorem tgR_edge_succ {x : RM T m AA} {ν : Bool} {j : Fin J} {e' : T.Ed (j + 1)}
    (hx : tgR T R ch x ν = .edge j.succ e') : ∃ e, x = .mid j e 2 ∧ ν = false ∧ T.πE e = e' := by
  rcases x with ⟨a, c, γ, s⟩ | ⟨j', i, e⟩ | ⟨j', e, s⟩ | e
  · exfalso
    have : ∀ e : Option (T.Ed 0), (edgeO T e : Tg T m AA) ≠ .edge j.succ e' := by
      intro e he
      cases e
      · simp [edgeO] at he
      · exact absurd (Tg.edge.inj he).1.symm (Fin.succ_ne_zero j)
    cases ν
    · exact this _ hx
    · simp only [tgR] at hx
      split_ifs at hx
      · exact this _ hx
  · simp [tgR] at hx
  · cases ν
    · fin_cases s
      · simp [tgR] at hx
      · simp [tgR] at hx
      · simp only [tgR, Fin.reduceFinMk, Matrix.cons_val, Tg.edge.injEq] at hx
        obtain ⟨h1, h2⟩ := hx
        have hj : j' = j := Fin.succ_injective _ h1
        subst hj
        exact ⟨e, rfl, rfl, eq_of_heq h2⟩
      · simp [tgR] at hx
    · fin_cases s
      · simp only [tgR, Fin.zero_eta, Matrix.cons_val_zero] at hx
        split_ifs at hx
      · simp [tgR] at hx
      · simp only [tgR, Fin.reduceFinMk, Matrix.cons_val] at hx
        split_ifs at hx
      · simp [tgR] at hx
  · simp [tgR] at hx

theorem tgR_seg {x : RM T m AA} {ν : Bool} {j : Fin J} {i : Fin h} {ω : T.V (j + 1) i} {q : Sym2 T.Fl}
    (hx : tgR T R ch x ν = .seg j i ω q) : ∃ e : T.Ed j, ν = false ∧ T.ty e = i ∧
      ((x = .mid j e 1 ∧ (T.πV (T.vx i (T.e0 e)) : T.V (j + 1) i) = ω ∧ s(T.co i (hst T i (T.e0 e)), T.co i (T.e0 e)) = q) ∨
      (x = .mid j e 3 ∧ (T.πV (T.vx i (T.e1 e)) : T.V (j + 1) i) = ω ∧ s(T.co i (hst T i (T.e1 e)), T.co i (T.e1 e)) = q)) := by
  rcases x with ⟨a, c, γ, s⟩ | ⟨j', i', e⟩ | ⟨j', e, s⟩ | e
  · exfalso
    have : ∀ e : Option (T.Ed 0), (edgeO T e : Tg T m AA) ≠ .seg j i ω q := by
      intro e he
      cases e <;> simp [edgeO] at he
    cases ν
    · exact this _ hx
    · simp only [tgR] at hx
      split_ifs at hx
      · exact this _ hx
  · simp [tgR] at hx
  · cases ν
    · fin_cases s
      · simp [tgR] at hx
      · simp only [tgR, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Tg.seg.injEq] at hx
        obtain ⟨h1, h2, h3, h4⟩ := hx
        subst h1
        subst h2
        exact ⟨e, rfl, rfl, Or.inl ⟨rfl, eq_of_heq h3, h4⟩⟩
      · simp [tgR] at hx
      · simp only [tgR, Fin.reduceFinMk, Matrix.cons_val, Tg.seg.injEq] at hx
        obtain ⟨h1, h2, h3, h4⟩ := hx
        subst h1
        subst h2
        exact ⟨e, rfl, rfl, Or.inr ⟨rfl, eq_of_heq h3, h4⟩⟩
    · fin_cases s
      · simp only [tgR, Fin.zero_eta, Matrix.cons_val_zero] at hx
        split_ifs at hx
      · simp [tgR] at hx
      · simp only [tgR, Fin.reduceFinMk, Matrix.cons_val] at hx
        split_ifs at hx
      · simp [tgR] at hx
  · simp [tgR] at hx

theorem tgR_mid {x : RM T m AA} {ν : Bool} {j : Fin J} {e : T.Ed j} {s : Fin 4}
    (hx : tgR T R ch x ν = .nxt (.mid j e s)) : ν = true ∧
      ((s = 1 ∧ x = .mid j e 0) ∨
      (s = 2 ∧ ((x = .mid j e 0 ∧ hst T (T.ty e) (T.e0 e) = T.π (T.e0 e)) ∨ x = .mid j e 1)) ∨
      (s = 3 ∧ x = .mid j e 2)) := by
  rcases x with ⟨a, c, γ, s'⟩ | ⟨j', i', e'⟩ | ⟨j', e', s'⟩ | e'
  · exfalso
    have : ∀ e' : Option (T.Ed 0), (edgeO T e' : Tg T m AA) ≠ .nxt (.mid j e s) := by
      intro e' he
      cases e' <;> simp [edgeO] at he
    cases ν
    · exact this _ hx
    · simp only [tgR] at hx
      split_ifs at hx
      · simp at hx
      · exact this _ hx
  · simp [tgR] at hx
  · cases ν
    · fin_cases s' <;> simp [tgR] at hx
    · refine ⟨rfl, ?_⟩
      fin_cases s'
      · simp only [tgR, Fin.zero_eta, Matrix.cons_val_zero] at hx
        split_ifs at hx with hh
        · simp only [Tg.nxt.injEq, RM.mid.injEq] at hx
          obtain ⟨h1, h2, h3⟩ := hx
          subst h1
          have := eq_of_heq h2
          subst this
          exact Or.inl ⟨h3.symm, rfl⟩
        · simp only [Tg.nxt.injEq, RM.mid.injEq] at hx
          obtain ⟨h1, h2, h3⟩ := hx
          subst h1
          have := eq_of_heq h2
          subst this
          rw [not_not] at hh
          exact Or.inr (Or.inl ⟨h3.symm, Or.inl ⟨rfl, hh⟩⟩)
      · simp only [tgR, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Tg.nxt.injEq, RM.mid.injEq] at hx
        obtain ⟨h1, h2, h3⟩ := hx
        subst h1
        have := eq_of_heq h2
        subst this
        exact Or.inr (Or.inl ⟨h3.symm, Or.inr rfl⟩)
      · simp only [tgR, Fin.reduceFinMk, Matrix.cons_val] at hx
        split_ifs at hx with hh
        simp only [Tg.nxt.injEq, RM.mid.injEq] at hx
        obtain ⟨h1, h2, h3⟩ := hx
        subst h1
        have := eq_of_heq h2
        subst this
        exact Or.inr (Or.inr ⟨h3.symm, rfl⟩)
      · simp [tgR] at hx
  · simp [tgR] at hx

end Targets

theorem sum_union_le {κ : Type*} [DecidableEq κ] (s t : Finset κ) (f : κ → ℕ) :
    ∑ x ∈ s ∪ t, f x ≤ ∑ x ∈ s, f x + ∑ x ∈ t, f x := by
  rw [← Finset.sum_union_inter]
  exact Nat.le_add_right _ _

theorem sum_biUnion_le' {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] (s : Finset ι) (t : ι → Finset κ) (f : κ → ℕ) :
    ∑ x ∈ s.biUnion t, f x ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    exact (sum_union_le _ _ _).trans (Nat.add_le_add_left ih _)

/-- The end segments on a pair, by edges. -/
theorem nEnd_eq {j : ℕ} {i : Fin h} (n : T.Ed j → ℕ) (ω : T.V (j + 1) i) (q : Sym2 T.Fl) : T.nEnd i n ω q =
    (∑ e : T.Ed j, if T.ty e = i ∧ T.πV (T.vx i (T.e0 e)) = ω ∧
      s(T.co i (T.host i (T.vx i (T.e0 e))), T.co i (T.e0 e)) = q then n e else 0) +
    ∑ e : T.Ed j, if T.ty e = i ∧ T.πV (T.vx i (T.e1 e)) = ω ∧
      s(T.co i (T.host i (T.vx i (T.e1 e))), T.co i (T.e1 e)) = q then n e else 0 := by
  unfold Tower.nEnd
  have e2 : ∀ c : T.X j, (if T.πV (T.vx i c) = ω ∧ s(T.co i (T.host i (T.vx i c)), T.co i c) = q then T.be i n c else 0) =
      ∑ e : T.Ed j, ((if T.e0 e = c then (if T.ty e = i ∧ T.πV (T.vx i (T.e0 e)) = ω ∧
        s(T.co i (T.host i (T.vx i (T.e0 e))), T.co i (T.e0 e)) = q then n e else 0) else 0) +
        if T.e1 e = c then (if T.ty e = i ∧ T.πV (T.vx i (T.e1 e)) = ω ∧
        s(T.co i (T.host i (T.vx i (T.e1 e))), T.co i (T.e1 e)) = q then n e else 0) else 0) := by
    intro c
    unfold Tower.be
    by_cases hc : T.πV (T.vx i c) = ω ∧ s(T.co i (T.host i (T.vx i c)), T.co i c) = q
    · rw [if_pos hc]
      refine Finset.sum_congr rfl fun e _ => ?_
      have hne := T.e_ne e
      by_cases h0 : T.e0 e = c
      · have h1 : ¬ T.e1 e = c := fun hh => hne (h0.trans hh.symm)
        subst h0
        by_cases ht : T.ty e = i
        · rw [if_pos ⟨ht, Or.inl rfl⟩, if_pos rfl, if_pos ⟨ht, hc⟩, if_neg h1, Nat.add_zero]
        · rw [if_neg fun hh => ht hh.1, if_pos rfl, if_neg fun hh => ht hh.1, if_neg h1, Nat.add_zero]
      · rw [if_neg h0, Nat.zero_add]
        by_cases h1 : T.e1 e = c
        · subst h1
          by_cases ht : T.ty e = i
          · rw [if_pos ⟨ht, Or.inr rfl⟩, if_pos rfl, if_pos ⟨ht, hc⟩]
          · rw [if_neg fun hh => ht hh.1, if_pos rfl, if_neg fun hh => ht hh.1]
        · rw [if_neg h1, if_neg]
          rintro ⟨-, hh | hh⟩
          · exact h0 hh
          · exact h1 hh
    · rw [if_neg hc]
      symm
      refine Finset.sum_eq_zero fun e _ => ?_
      rw [Nat.add_eq_zero_iff]
      constructor
      · by_cases h0 : T.e0 e = c
        · subst h0
          rw [if_pos rfl, if_neg fun hh => hc hh.2]
        · rw [if_neg h0]
      · by_cases h0 : T.e1 e = c
        · subst h0
          rw [if_pos rfl, if_neg fun hh => hc hh.2]
        · rw [if_neg h0]
  rw [Finset.sum_congr rfl fun c _ => e2 c, Finset.sum_comm, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq, if_pos (mem_univ _), if_pos (mem_univ _)]

section Mid

variable (hr : 0 < r) (hb : 0 < b)
include hr hb

theorem num_inl (x : {x : RM T m AA // okR T R ch x}) : num R ch FL lhat n o (.inl x) ≤
    load R ch FL lhat n o (inpR T x.1) := by
  classical
  rw [num_eq hr hb, numF]
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _

theorem num_mid0 (j : Fin J) (e : T.Ed j) (hx : okR T R ch (.mid j e 0)) :
    num R ch FL lhat n o (.inl ⟨.mid j e 0, hx⟩) ≤ load R ch FL lhat n o (.edge j.castSucc e) ∧
    (¬ IsMin (load R ch FL lhat n o) j.castSucc (T.ty e) → num R ch FL lhat n o (.inl ⟨.mid j e 0, hx⟩) = 0) := by
  classical
  refine ⟨num_inl hr hb _, fun hn => ?_⟩
  rw [num_eq hr hb, numF, if_neg]
  intro ha
  exact hn (ha rfl)

/-- The relays of an edge are given at most what is on the edge. -/
theorem num_mid_le (j : Fin J) (e : T.Ed j) (s : Fin 4) (hx : okR T R ch (.mid j e s)) :
    ∃ hx0 : okR T R ch (.mid j e 0), num R ch FL lhat n o (.inl ⟨.mid j e s, hx⟩) ≤
      num R ch FL lhat n o (.inl ⟨.mid j e 0, hx0⟩) := by
  have hx0 : okR T R ch (.mid j e 0) := ⟨fun hh => absurd hh (by decide), fun hh => absurd hh (by decide)⟩
  refine ⟨hx0, ?_⟩
  have one : ∀ hx1 : okR T R ch (.mid j e 1), num R ch FL lhat n o (.inl ⟨.mid j e 1, hx1⟩) ≤
      num R ch FL lhat n o (.inl ⟨.mid j e 0, hx0⟩) := by
    intro hx1
    refine (num_inl hr hb _).trans ?_
    refine (load_le_sum {(⟨.inl ⟨.mid j e 0, hx0⟩, true⟩ : NM R FL (ch := ch))} (bt_mid j e 1) ?_).trans ?_
    · rintro ⟨⟨x, hx'⟩ | l, ν⟩ hν -
      · obtain ⟨h1, h2⟩ := tgR_mid (x := x) (ν := ν) hν
        have h3 : x = .mid j e 0 := by
          rcases h2 with h2 | h2 | h2
          · exact h2.2
          · exact absurd h2.1 (by decide)
          · exact absurd h2.1 (by decide)
        subst h3
        have h1 : ν = true := h1
        subst h1
        exact mem_singleton_self _
      · simp [tgM, inpR_mid] at hν
    · rw [Finset.sum_singleton]
      exact alv_le_num hr hb _ _
  have two : ∀ hx2 : okR T R ch (.mid j e 2), num R ch FL lhat n o (.inl ⟨.mid j e 2, hx2⟩) ≤
      num R ch FL lhat n o (.inl ⟨.mid j e 0, hx0⟩) := by
    intro hx2
    refine (num_inl hr hb _).trans ?_
    by_cases hh : hst T (T.ty e) (T.e0 e) = T.π (T.e0 e)
    · refine (load_le_sum {(⟨.inl ⟨.mid j e 0, hx0⟩, true⟩ : NM R FL (ch := ch))} (bt_mid j e 2) ?_).trans ?_
      · rintro ⟨⟨x, hx'⟩ | l, ν⟩ hν -
        · obtain ⟨h1, h2⟩ := tgR_mid (x := x) (ν := ν) hν
          have h3 : x = .mid j e 0 := by
            rcases h2 with h2 | h2 | h2
            · exact h2.2
            · rcases h2.2 with h3 | h3
              · exact h3.1
              · subst h3
                exact absurd hh (hx'.1 rfl)
            · exact absurd h2.1 (by decide)
          subst h3
          have h1 : ν = true := h1
          subst h1
          exact mem_singleton_self _
        · simp [tgM, inpR_mid] at hν
      · rw [Finset.sum_singleton]
        exact alv_le_num hr hb _ _
    · have hx1 : okR T R ch (.mid j e 1) := ⟨fun _ => hh, fun h3 => absurd h3 (by decide)⟩
      refine (load_le_sum {(⟨.inl ⟨.mid j e 1, hx1⟩, true⟩ : NM R FL (ch := ch))} (bt_mid j e 2) ?_).trans ?_
      · rintro ⟨⟨x, hx'⟩ | l, ν⟩ hν -
        · obtain ⟨h1, h2⟩ := tgR_mid (x := x) (ν := ν) hν
          have h3 : x = .mid j e 1 := by
            rcases h2 with h2 | h2 | h2
            · exact absurd h2.1 (by decide)
            · rcases h2.2 with h3 | h3
              · exact absurd h3.2 hh
              · exact h3
            · exact absurd h2.1 (by decide)
          subst h3
          have h1 : ν = true := h1
          subst h1
          exact mem_singleton_self _
        · simp [tgM, inpR_mid] at hν
      · rw [Finset.sum_singleton]
        exact (alv_le_num hr hb _ _).trans (one hx1)
  fin_cases s
  · exact le_rfl
  · exact one hx
  · exact two hx
  · have hx2 : okR T R ch (.mid j e 2) := ⟨fun hh => absurd hh (by decide), fun hh => absurd hh (by decide)⟩
    refine (num_inl hr hb _).trans ?_
    refine (load_le_sum {(⟨.inl ⟨.mid j e 2, hx2⟩, true⟩ : NM R FL (ch := ch))} (bt_mid j e 3) ?_).trans ?_
    · rintro ⟨⟨x, hx'⟩ | l, ν⟩ hν -
      · obtain ⟨h1, h2⟩ := tgR_mid (x := x) (ν := ν) hν
        have h3 : x = .mid j e 2 := by
          rcases h2 with h2 | h2 | h2
          · exact absurd h2.1 (by decide)
          · exact absurd h2.1 (by decide)
          · exact h2.2
        subst h3
        have h1 : ν = true := h1
        subst h1
        exact mem_singleton_self _
      · simp [tgM, inpR_mid] at hν
    · rw [Finset.sum_singleton]
      exact (alv_le_num hr hb _ _).trans (two hx2)

theorem alv_mid_le (j : Fin J) (e : T.Ed j) (s : Fin 4) (hx : okR T R ch (.mid j e s)) (ν : Bool) :
    alv R ch FL lhat n o (⟨.inl ⟨.mid j e s, hx⟩, ν⟩ : NM R FL (ch := ch)) ≤ load R ch FL lhat n o (.edge j.castSucc e) ∧
    (¬ IsMin (load R ch FL lhat n o) j.castSucc (T.ty e) →
      alv R ch FL lhat n o (⟨.inl ⟨.mid j e s, hx⟩, ν⟩ : NM R FL (ch := ch)) = 0) := by
  obtain ⟨hx0, h1⟩ := num_mid_le (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb j e s hx
  have h2 := num_mid0 (FL := FL) (lhat := lhat) (n := n) (o := o) hr hb j e hx0
  have h3 := alv_le_num (lhat := lhat) (n := n) (o := o) hr hb (⟨.mid j e s, hx⟩ : {x : RM T m AA // okR T R ch x}) ν
  refine ⟨h3.trans (h1.trans h2.1), fun hn => ?_⟩
  have := h2.2 hn
  omega

/-- The channels of end segments. -/
theorem seg_chan {j : Fin J} {i : Fin h} {ω : T.V (j + 1) i} {q : Sym2 T.Fl} {ν : NM R FL (ch := ch)}
    (hν : tgM R ch FL ν.1 ν.2 = .seg j i ω q) : ∃ (e : T.Ed j) (s : Fin 4) (hx : okR T R ch (.mid j e s)),
      T.ty e = i ∧ ν = ⟨.inl ⟨.mid j e s, hx⟩, false⟩ ∧
      ((s = 1 ∧ T.πV (T.vx i (T.e0 e)) = ω ∧ s(T.co i (T.host i (T.vx i (T.e0 e))), T.co i (T.e0 e)) = q) ∨
      (s = 3 ∧ T.πV (T.vx i (T.e1 e)) = ω ∧ s(T.co i (T.host i (T.vx i (T.e1 e))), T.co i (T.e1 e)) = q)) := by
  rcases ν with ⟨⟨x, hx⟩ | l, ν⟩
  · obtain ⟨e, h1, h2, h3⟩ := tgR_seg (x := x) (ν := ν) hν
    have h1 : ν = false := h1
    subst h1
    rcases h3 with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · subst h3
      exact ⟨e, 1, hx, h2, rfl, Or.inl ⟨rfl, h4⟩⟩
    · subst h3
      exact ⟨e, 3, hx, h2, rfl, Or.inr ⟨rfl, h4⟩⟩
  · simp [tgM] at hν

/-- End segments, inactive types. -/
theorem seg_zero {j : Fin J} {i : Fin h} (hn : ¬ IsMin (load R ch FL lhat n o) j.castSucc i) (ω : T.V (j + 1) i)
    (q : Sym2 T.Fl) : load R ch FL lhat n o (.seg j i ω q) = 0 := by
  rw [load_def, bt_seg, Nat.zero_add]
  refine Finset.sum_eq_zero fun ν _ => ?_
  split_ifs with hν
  · obtain ⟨e, s, hx, h1, h2, -⟩ := seg_chan hr hb hν
    rw [h2]
    exact (alv_mid_le hr hb j e s hx false).2 (by rw [h1]; exact hn)
  · rfl

open Classical in
/-- The channel of an end segment. -/
noncomputable def segS (j : Fin J) (s : Fin 4) (e : T.Ed j) : Finset (NM R FL (ch := ch)) :=
  if hx : okR T R ch (.mid j e s) then {⟨.inl ⟨.mid j e s, hx⟩, false⟩} else ∅

theorem sum_segS (j : Fin J) (s : Fin 4) (e : T.Ed j) : ∑ ν ∈ segS (R := R) (ch := ch) (FL := FL) j s e, alv R ch FL lhat n o ν ≤
    load R ch FL lhat n o (.edge j.castSucc e) := by
  unfold segS
  split_ifs with hx
  · rw [Finset.sum_singleton]
    exact (alv_mid_le hr hb j e s hx false).1
  · rw [Finset.sum_empty]
    exact Nat.zero_le _

/-- End segments. -/
theorem seg_le (j : Fin J) (i : Fin h) (ω : T.V (j + 1) i) (q : Sym2 T.Fl) :
    load R ch FL lhat n o (.seg j i ω q) ≤ T.nEnd i (fun e => load R ch FL lhat n o (.edge j.castSucc e)) ω q := by
  classical
  rw [nEnd_eq]
  refine (load_le_sum
    (((univ.filter fun e : T.Ed j => T.ty e = i ∧ T.πV (T.vx i (T.e0 e)) = ω ∧
      s(T.co i (T.host i (T.vx i (T.e0 e))), T.co i (T.e0 e)) = q).biUnion (segS (R := R) (ch := ch) (FL := FL) j 1)) ∪
    ((univ.filter fun e : T.Ed j => T.ty e = i ∧ T.πV (T.vx i (T.e1 e)) = ω ∧
      s(T.co i (T.host i (T.vx i (T.e1 e))), T.co i (T.e1 e)) = q).biUnion (segS (R := R) (ch := ch) (FL := FL) j 3)))
    (bt_seg j i ω q) ?_).trans ?_
  · intro ν hν _
    obtain ⟨e, s, hx, h1, h2, h3⟩ := seg_chan hr hb hν
    rcases h3 with ⟨h5, h6⟩ | ⟨h5, h6⟩
    · subst h5
      refine mem_union_left _ (mem_biUnion.2 ⟨e, mem_filter.2 ⟨mem_univ _, h1, h6⟩, ?_⟩)
      unfold segS
      rw [dif_pos hx, h2]
      exact mem_singleton_self _
    · subst h5
      refine mem_union_right _ (mem_biUnion.2 ⟨e, mem_filter.2 ⟨mem_univ _, h1, h6⟩, ?_⟩)
      unfold segS
      rw [dif_pos hx, h2]
      exact mem_singleton_self _
  · refine (sum_union_le _ _ _).trans (add_le_add ?_ ?_)
    · refine (sum_biUnion_le' _ _ _).trans ?_
      rw [Finset.sum_filter]
      refine Finset.sum_le_sum fun e _ => ?_
      split_ifs
      · exact sum_segS hr hb j 1 e
      · exact le_rfl
    · refine (sum_biUnion_le' _ _ _).trans ?_
      rw [Finset.sum_filter]
      refine Finset.sum_le_sum fun e _ => ?_
      split_ifs
      · exact sum_segS hr hb j 3 e
      · exact le_rfl

end Mid

end Nc.Tow
