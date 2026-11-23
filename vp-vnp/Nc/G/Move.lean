/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.G.Contract
import Nc.Cut.Codes

/-!
# The identity of one move, for general laws
-/

set_option linter.unusedSectionVars false

namespace Nc.G

open Finset Nc.Cut

variable {F : Type} [CommRing F] {A A' E U0 U1 ub : ℕ} {M : Sys F (A + A') E}

section Slots

variable {N : Type} [Fintype N] [DecidableEq N]

theorem length_uwBits {w : UW ub} (h : w ≠ none) : (uwBits w).length = ub := by
  obtain ⟨v, rfl⟩ := Option.ne_none_iff_exists'.1 h
  simp [uwBits]

theorem uwBits_inj {w w' : UW ub} (h : w ≠ none) (h' : w' ≠ none) (e : uwBits w = uwBits w') : w = w' := by
  obtain ⟨v, rfl⟩ := Option.ne_none_iff_exists'.1 h
  obtain ⟨v', rfl⟩ := Option.ne_none_iff_exists'.1 h'
  rw [List.ofFn_injective e]

theorem length_uwList {ids : List (Uid A U0 N U1)} {y : Uid A U0 N U1 → UW ub} (h : ∀ id ∈ ids, y id ≠ none) :
    (ids.flatMap fun id => uwBits (y id)).length = ids.length * ub := by
  induction ids with
  | nil => simp
  | cons id ids ih =>
    rw [List.flatMap_cons, List.length_append, length_uwBits (h id List.mem_cons_self),
      ih fun i hi => h i (List.mem_cons_of_mem _ hi), List.length_cons]
    ring

theorem length_slotBits {t : ℕ} {ids : List (Uid A U0 N U1)} {y : Uid A U0 N U1 → UW ub} (h : ∀ id ∈ ids, y id ≠ none)
    (ht : ids.length ≤ t) : (slotBits t ids y).length = t * ub := by
  rw [slotBits, List.length_append, length_uwList h, List.length_replicate, ← add_mul, Nat.add_sub_cancel' ht]

theorem uwList_inj {ids : List (Uid A U0 N U1)} {y y' : Uid A U0 N U1 → UW ub} (h : ∀ id ∈ ids, y id ≠ none)
    (h' : ∀ id ∈ ids, y' id ≠ none)
    (e : (ids.flatMap fun id => uwBits (y id)) = ids.flatMap fun id => uwBits (y' id)) : ∀ id ∈ ids, y id = y' id := by
  induction ids with
  | nil => simp
  | cons id ids ih =>
    rw [List.flatMap_cons, List.flatMap_cons] at e
    obtain ⟨e1, e2⟩ := List.append_inj e (by
      rw [length_uwBits (h id List.mem_cons_self), length_uwBits (h' id List.mem_cons_self)])
    intro i hi
    rcases List.mem_cons.1 hi with rfl | hi
    · exact uwBits_inj (h _ List.mem_cons_self) (h' _ List.mem_cons_self) e1
    · exact ih (fun i hi => h i (List.mem_cons_of_mem _ hi)) (fun i hi => h' i (List.mem_cons_of_mem _ hi)) e2 i hi

/-- Two copies of a slot agree if the units do. -/
theorem slotBits_eq_iff {t : ℕ} {ids : List (Uid A U0 N U1)} {y y' : Uid A U0 N U1 → UW ub}
    (h : ∀ id ∈ ids, y id ≠ none) (h' : ∀ id ∈ ids, y' id ≠ none) (ht : ids.length ≤ t) :
    (∀ k : Fin (t * ub), (slotBits t ids y).getD k false = (slotBits t ids y').getD k false) ↔
      ∀ id ∈ ids, y id = y' id := by
  constructor
  · intro hk
    have e : slotBits t ids y = slotBits t ids y' := by
      apply List.ext_getElem
      · rw [length_slotBits h ht, length_slotBits h' ht]
      · intro k h1 h2
        have := hk ⟨k, by rwa [length_slotBits h ht] at h1⟩
        rwa [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this
    unfold slotBits at e
    exact uwList_inj h h' (List.append_inj e (by rw [length_uwList h, length_uwList h'])).1
  · intro hk k
    have : slotBits t ids y = slotBits t ids y' := by
      unfold slotBits
      congr 1
      exact List.flatMap_congr fun id hid => by rw [hk id hid]
    rw [this]

theorem slotBits_congr {t : ℕ} {ids : List (Uid A U0 N U1)} {y y' : Uid A U0 N U1 → UW ub}
    (h : ∀ id ∈ ids, y id = y' id) : slotBits t ids y = slotBits t ids y' := by
  unfold slotBits
  congr 1
  exact List.flatMap_congr fun id hid => by rw [h id hid]

end Slots

section Role

/-- The role depends on the units given and on the new units at its channels only. -/
theorem role_congr {x : Fin E} {p : (M.kind x).Ro} {t : ℕ} {ids : (M.kind x).SlAt p → List (Uid A U0 M.N U1)}
    {o o' : M.N → Fin U1} {y y' : Uid A U0 M.N U1 → UW ub} (ho : ∀ ν, o ⟨x, ν⟩ = o' ⟨x, ν⟩)
    (h1 : ∀ e, ∀ id ∈ ids e, y id = y' id)
    (h2 : ∀ ν : (M.kind x).CnAt p, ∀ k, y (.new ⟨x, ν.1⟩ k) = y' (.new ⟨x, ν.1⟩ k)) :
    role M x p t ids o y = role M x p t ids o' y' := by
  classical
  unfold role
  refine if_congr (forall_congr' fun e => forall₂_congr fun id hid => by rw [h1 e id hid]) ?_ rfl
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun g _ => ?_
  refine if_congr (forall_congr' fun ν => ?_) ?_ rfl
  · unfold ChOk
    rw [ho]
    exact and_congr_right fun _ => forall_congr' fun k => by rw [h2 ν k]
  · refine Finset.prod_congr rfl fun k _ => ?_
    congr 1
    funext e
    rw [slotBits_congr (h1 e)]

theorem role_ne_zero {x : Fin E} {p : (M.kind x).Ro} {t : ℕ} {ids : (M.kind x).SlAt p → List (Uid A U0 M.N U1)}
    {o : M.N → Fin U1} {y : Uid A U0 M.N U1 → UW ub} (h : role M x p t ids o y ≠ 0) :
    (∀ e, ∀ id ∈ ids e, y id ≠ none) ∧ ∃ (i : Fin (t * ub) → (M.kind x).I)
      (g : ∀ k, ∀ ν : (M.kind x).CnAt p, Fin ((M.kind x).len (i k) ν) → Bool),
      (∀ ν : (M.kind x).CnAt p, ChOk ⟨x, ν.1⟩ (o ⟨x, ν.1⟩).1
        (chString (M.kind x).lab (fun j => (M.kind x).len j ν) i fun k => g k ν) y) ∧
      ∏ k : Fin (t * ub), (M.kind x).tab p (i k) (fun e => (slotBits t (ids e) y).getD k false) (g k) ≠ 0 := by
  classical
  rw [role] at h
  split_ifs at h with hy
  swap
  · exact absurd rfl h
  obtain ⟨i, -, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨g, -, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  split_ifs at h with hc
  · exact ⟨hy, i, g, hc, h⟩
  · exact absurd rfl h

theorem ChOk.ne_none {N : Type} {ν : N} {J : ℕ} {str : List Bool} {y : Uid A U0 N U1 → UW ub} (h : ChOk ν J str y)
    {k : Fin U1} (hk : k.1 ≤ J) : y (.new ν k) ≠ none := by
  rw [h.2 k, Ne, unitsOf_eq_none, h.1]
  omega

/-- The roles at the ends of a channel force its new units to be present. -/
theorem role_new_ne_none {x : Fin E} {p : (M.kind x).Ro} {t : ℕ} {ids : (M.kind x).SlAt p → List (Uid A U0 M.N U1)}
    {o : M.N → Fin U1} {y : Uid A U0 M.N U1 → UW ub} (h : role M x p t ids o y ≠ 0) {ν : (M.kind x).Cn}
    (hν : (M.kind x).c ν = p ∨ (M.kind x).d ν = p) {k : Fin U1} (hk : k ≤ o ⟨x, ν⟩) : y (.new ⟨x, ν⟩ k) ≠ none := by
  obtain ⟨-, i, g, hg, -⟩ := role_ne_zero h
  exact (hg ⟨ν, hν⟩).ne_none hk

end Role

section Law

variable (L : Law F)

/-- The code word of the string on a channel: its first `U1` units. -/
def chCode (ub U1 B : ℕ) (ν : L.Cn) (i : Fin B → L.I) (g : (k : Fin B) → Fin (L.len (i k) ν) → Bool) : Fin U1 → UW ub :=
  fun k => unitsOf ub (chString L.lab (fun j => L.len j ν) i g) k

theorem length_chString {I : Type} {lam B : ℕ} (lb : I → Fin lam → Bool) (len : I → ℕ) (i : Fin B → I)
    (g : ∀ k, Fin (len (i k)) → Bool) : (chString lb len i g).length = ∑ k, (lam + len (i k)) :=
  length_sideString lb len i g

/-- A bound for the lengths of the strings of a law. -/
structure Law.Le (L : Law F) (m : ℕ) : Prop where
  len_le : ∀ i ν, L.len i ν ≤ m

variable {L}

theorem chCode_injective (hub : 0 < ub) {m B : ℕ} (hm : L.Le m) (hB : B * (m + L.lam) / ub + 1 ≤ U1) (ν : L.Cn) :
    Function.Injective fun q : Σ i : Fin B → L.I, (k : Fin B) → Fin (L.len (i k) ν) → Bool =>
      chCode L ub U1 B ν q.1 q.2 :=
  codeWord_injective (len := fun i => L.len i ν) L.lab_inj hub (fun i => hm.len_le i ν) hB

open Classical in
variable (L) in
/-- The table of the law for an outcome; `X p k e` are the bits. -/
noncomputable def outTab (ub : ℕ) {U1 B : ℕ} (X : L.Ro → Fin B → L.Sl → Bool) (o : L.Cn → Fin U1) (p : L.Ro)
    (i : Fin B → L.I) (g : (ν : L.CnAt p) → (k : Fin B) → Fin (L.len (i k) ν) → Bool) : F :=
  if ∀ ν : L.CnAt p, ucount ub (chString L.lab (fun j => L.len j ν) i (g ν)) = (o ν).1 + 1 then
    ∏ k, L.tab p (i k) (fun e => X p k e) fun ν => g ν k else 0

/-- Tables with code words, summed over all outcomes. -/
theorem sum_outTab (hub : 0 < ub) {m B : ℕ} (hm : L.Le m) (hB : B * (m + L.lam) / ub + 1 ≤ U1)
    (X : L.Ro → Fin B → L.Sl → Bool) :
    (∑ o : L.Cn → Fin U1, ∑ z : L.Cn → Fin U1 → UW ub, ∏ p, codeTab L.c L.d (chCode L ub U1 B) p (outTab L ub X o p) z) =
      if ∀ e k, X (L.a e) k e = X (L.b e) k e then 1 else 0 := by
  classical
  rcases isEmpty_or_nonempty L.Ro with hRo | hRo
  · have hCn : IsEmpty L.Cn := ⟨fun ν => hRo.elim (L.c ν)⟩
    have hSl : IsEmpty L.Sl := ⟨fun e => hRo.elim (L.a e)⟩
    rw [if_pos fun e => hSl.elim e]
    simp
  have e1 : ∀ o : L.Cn → Fin U1, (∑ z : L.Cn → Fin U1 → UW ub,
      ∏ p, codeTab L.c L.d (chCode L ub U1 B) p (outTab L ub X o p) z) =
      ∑ i : Fin B → L.I, ∑ g : (ν : L.Cn) → (k : Fin B) → Fin (L.len (i k) ν) → Bool,
        ∏ p, outTab L ub X o p i fun ν => g ν := fun o =>
    contract (fun ν => chCode_injective hub hm hB ν) (L.conn_pow B) (outTab L ub X o)
  simp only [e1]
  let cnt : (Fin B → L.I) → L.Cn → ℕ := fun i ν => (∑ k, (L.lam + L.len (i k) ν)) / ub
  have hcnt : ∀ (i : Fin B → L.I) ν (g : (k : Fin B) → Fin (L.len (i k) ν) → Bool),
      ucount ub (chString L.lab (fun j => L.len j ν) i g) = cnt i ν + 1 := by
    intro i ν g
    rw [ucount, length_chString]
  have hlt : ∀ i ν, cnt i ν < U1 := by
    intro i ν
    refine lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.div_le_div_right ?_)) hB
    calc ∑ k, (L.lam + L.len (i k) ν) ≤ ∑ _k : Fin B, (m + L.lam) :=
          Finset.sum_le_sum fun k _ => by have := hm.len_le (i k) ν; omega
      _ = B * (m + L.lam) := by simp
  have e2 : ∀ (o : L.Cn → Fin U1) i (g : (ν : L.Cn) → (k : Fin B) → Fin (L.len (i k) ν) → Bool),
      (∏ p, outTab L ub X o p i fun ν => g ν) = if o = fun ν => ⟨cnt i ν, hlt i ν⟩ then
        ∏ p, ∏ k, L.tab p (i k) (fun e => X p k e) (fun ν => g ν k) else 0 := by
    intro o i g
    unfold outTab
    rw [Finset.prod_ite_zero]
    have key : (∀ p ∈ (univ : Finset L.Ro), ∀ ν : L.CnAt p,
        ucount ub (chString L.lab (fun j => L.len j ν) i (g ν)) = (o ν).1 + 1) ↔
        o = fun ν => (⟨cnt i ν, hlt i ν⟩ : Fin U1) := by
      simp only [Finset.mem_univ, true_imp_iff, hcnt]
      constructor
      · intro h
        funext ν
        have := h (L.c ν) ⟨ν, Or.inl rfl⟩
        exact Fin.ext (by simpa using this.symm)
      · rintro rfl p ν
        rfl
    by_cases h : o = fun ν => (⟨cnt i ν, hlt i ν⟩ : Fin U1)
    · rw [if_pos h, if_pos (key.2 h)]
    · rw [if_neg h, if_neg fun h' => h (key.1 h')]
  simp only [e2]
  have swap : (∑ o : L.Cn → Fin U1, ∑ i : Fin B → L.I,
      ∑ g : (ν : L.Cn) → (k : Fin B) → Fin (L.len (i k) ν) → Bool,
      if o = fun ν => ⟨cnt i ν, hlt i ν⟩ then
        ∏ p, ∏ k, L.tab p (i k) (fun e => X p k e) (fun ν => g ν k) else 0) =
      ∑ i : Fin B → L.I, ∑ g : (ν : L.Cn) → (k : Fin B) → Fin (L.len (i k) ν) → Bool,
        ∏ p, ∏ k, L.tab p (i k) (fun e => X p k e) (fun ν => g ν k) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.sum_ite_eq']
    simp
  rw [swap, ← L.pow B X]

/-- Impossible outcomes contribute nothing. -/
theorem sum_codeTab_zero (hub : 0 < ub) {m B : ℕ} (hm : L.Le m) (hB : B * (m + L.lam) / ub + 1 ≤ U1)
    (X : L.Ro → Fin B → L.Sl → Bool) (o : L.Cn → Fin U1)
    (h : ¬ ∃ i : Fin B → L.I, ∀ ν, (o ν).1 = (∑ k, (L.lam + L.len (i k) ν)) / ub) :
    (∑ z : L.Cn → Fin U1 → UW ub, ∏ p, codeTab L.c L.d (chCode L ub U1 B) p (outTab L ub X o p) z) = 0 := by
  classical
  rcases isEmpty_or_nonempty L.Ro with hRo | hRo
  · have hCn : IsEmpty L.Cn := ⟨fun ν => hRo.elim (L.c ν)⟩
    have hSl : IsEmpty L.Sl := ⟨fun e => hRo.elim (L.a e)⟩
    have hI : IsEmpty (Fin B → L.I) := ⟨fun i => h ⟨i, fun ν => hCn.elim ν⟩⟩
    have := L.pow B X
    rw [if_pos fun e => hSl.elim e, Fintype.sum_empty] at this
    have h0 : ∀ a : F, a = 0 := fun a => by rw [← mul_one a, this, mul_zero]
    exact h0 _
  rw [contract (fun ν => chCode_injective hub hm hB ν) (L.conn_pow B) (outTab L ub X o)]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun g _ => ?_
  by_contra hne
  refine h ⟨i, fun ν => ?_⟩
  have h1 : outTab L ub X o (L.c ν) i (fun ν => g ν) ≠ 0 := fun h0 =>
    hne (Finset.prod_eq_zero (Finset.mem_univ (L.c ν)) h0)
  rw [outTab] at h1
  split_ifs at h1 with h2
  swap
  · exact absurd rfl h1
  have h3 := h2 ⟨ν, Or.inl rfl⟩
  rw [ucount, length_chString, Nat.add_right_cancel_iff] at h3
  exact h3.symm

end Law

section Identity

/-- The role as a table with code words. -/
theorem role_eq_codeTab {x : Fin E} {p : (M.kind x).Ro} {t : ℕ} {ids : (M.kind x).SlAt p → List (Uid A U0 M.N U1)}
    {o : M.N → Fin U1} {y : Uid A U0 M.N U1 → UW ub} (hy : ∀ e, ∀ id ∈ ids e, y id ≠ none)
    {X : (M.kind x).Ro → Fin (t * ub) → (M.kind x).Sl → Bool}
    (hX : ∀ k (e : (M.kind x).SlAt p), X p k e = (slotBits t (ids e) y).getD k false) :
    role M x p t ids o y = codeTab (M.kind x).c (M.kind x).d (chCode (M.kind x) ub U1 (t * ub)) p
      (outTab (M.kind x) ub X (fun ν => o ⟨x, ν⟩) p) (fun ν k => y (.new ⟨x, ν⟩ k)) := by
  classical
  rw [role, if_pos hy, codeTab]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Fintype.sum_equiv (Equiv.piComm fun (k : Fin (t * ub)) (ν : (M.kind x).CnAt p) =>
    Fin ((M.kind x).len (i k) ν) → Bool) _ _ fun g => ?_
  have e1 : ∀ ν : (M.kind x).CnAt p, ChOk ⟨x, ν.1⟩ (o ⟨x, ν.1⟩).1
      (chString (M.kind x).lab (fun j => (M.kind x).len j ν) i fun k => g k ν) y ↔
      chCode (M.kind x) ub U1 (t * ub) ν i (fun k => g k ν) = (fun k => y (.new ⟨x, ν.1⟩ k)) ∧
      ucount ub (chString (M.kind x).lab (fun j => (M.kind x).len j ν) i fun k => g k ν) = (o ⟨x, ν.1⟩).1 + 1 := by
    intro ν
    rw [ChOk, and_comm]
    refine and_congr_left fun _ => ?_
    rw [funext_iff]
    exact forall_congr' fun k => eq_comm
  have e2 : (∏ k : Fin (t * ub), (M.kind x).tab p (i k) (fun e => (slotBits t (ids e) y).getD k false) (g k)) =
      ∏ k, (M.kind x).tab p (i k) (fun e => X p k e) (fun ν => g k ν) := by
    refine Finset.prod_congr rfl fun k _ => ?_
    congr 1
    funext e
    exact (hX k e).symm
  rw [e2]
  by_cases h1 : ∀ ν : (M.kind x).CnAt p, chCode (M.kind x) ub U1 (t * ub) ν i (fun k => g k ν) =
    (fun k => y (.new ⟨x, ν.1⟩ k))
  · by_cases h2 : ∀ ν : (M.kind x).CnAt p, ucount ub (chString (M.kind x).lab (fun j => (M.kind x).len j ν) i
        fun k => g k ν) = (o ⟨x, ν.1⟩).1 + 1
    · refine (if_pos fun ν => (e1 ν).2 ⟨h1 ν, h2 ν⟩).trans (Eq.trans ?_ (if_pos h1).symm)
      exact (if_pos h2).symm
    · refine (if_neg fun h => h2 fun ν => ((e1 ν).1 (h ν)).2).trans (Eq.trans ?_ (if_pos h1).symm)
      exact (if_neg h2).symm
  · exact (if_neg fun h => h1 fun ν => ((e1 ν).1 (h ν)).1).trans (if_neg h1).symm

theorem new_mem_newUnits {x : Fin E} {o : M.N → Fin U1} {ν : M.N} {k : Fin U1} :
    (Uid.new ν k : Uid A U0 M.N U1) ∈ newUnits M x o ↔ ν.1 = x ∧ k ≤ o ν := by
  simp [newUnits]

theorem init_not_mem_newUnits {x : Fin E} {o : M.N → Fin U1} {a b : Fin A} {k : Fin U0} :
    (Uid.init a b k : Uid A U0 M.N U1) ∉ newUnits M x o := by
  simp [newUnits]

theorem holds_new {x : Fin E} {p : (M.kind x).Ro} {ν : (M.kind x).Cn}
    (hν : (M.kind x).c ν = p ∨ (M.kind x).d ν = p) (k : Fin U1) :
    Holds (hold0 M.np) (hold1 M.np) (M.part x p) (Uid.new ⟨x, ν⟩ k : Uid A U0 M.N U1) := by
  rcases hν with h | h
  · left
    show M.part x p = M.part x ((M.kind x).c ν)
    rw [h]
  · right
    show M.part x p = M.part x ((M.kind x).d ν)
    rw [h]

/-- Set the outcome of move `x`. -/
def upd (M : Sys F (A + A') E) (o : M.N → Fin U1) (x : Fin E) (oo : (M.kind x).Cn → Fin U1) : M.N → Fin U1 := fun ν =>
  if h : x = ν.1 then (h ▸ oo : (M.kind ν.1).Cn → Fin U1) ν.2 else o ν

theorem upd_self (o : M.N → Fin U1) (x : Fin E) (oo : (M.kind x).Cn → Fin U1) (ν : (M.kind x).Cn) :
    upd M o x oo ⟨x, ν⟩ = oo ν := by simp [upd]

theorem upd_ne (o : M.N → Fin U1) {x : Fin E} (oo : (M.kind x).Cn → Fin U1) {ν : M.N} (h : ν.1 ≠ x) :
    upd M o x oo ν = o ν := by
  rw [upd, dif_neg (Ne.symm h)]

/-- One outcome of a move, as a sum over code words. -/
theorem move_outcome (x : Fin E) {t : ℕ} (o : M.N → Fin U1) (Seen : Finset (Uid A U0 M.N U1))
    (hSeen : ∀ (ν : (M.kind x).Cn) k, Uid.new ⟨x, ν⟩ k ∉ Seen)
    {y : Fin (A + A') → Uid A U0 M.N U1 → UW ub} (hy : y ∈ Contents (hold0 M.np) (hold1 M.np) none Seen)
    (ids : (M.kind x).Sl → List (Uid A U0 M.N U1)) (hids : ∀ e, ∀ id ∈ ids e, id ∈ Seen) (ht : ∀ e, (ids e).length ≤ t)
    (hne : ∀ e, ∀ id ∈ ids e, y (M.part x ((M.kind x).a e)) id ≠ none ∧ y (M.part x ((M.kind x).b e)) id ≠ none)
    (oo : (M.kind x).Cn → Fin U1) :
    (∑ z ∈ Common none (newUnits M x (upd M o x oo)), ∏ p,
      role M x p t (fun e => ids e.1) (upd M o x oo)
        (ext (hold0 M.np) (hold1 M.np) (newUnits M x (upd M o x oo)) y z (M.part x p))) =
      ∑ z : (M.kind x).Cn → Fin U1 → UW ub, ∏ p, codeTab (M.kind x).c (M.kind x).d (chCode (M.kind x) ub U1 (t * ub)) p
        (outTab (M.kind x) ub (fun p k e => (slotBits t (ids e) (y (M.part x p))).getD k false) oo p) z := by
  classical
  set X : (M.kind x).Ro → Fin (t * ub) → (M.kind x).Sl → Bool := fun p k e =>
    (slotBits t (ids e) (y (M.part x p))).getD k false with hX
  set New : Finset (Uid A U0 M.N U1) := newUnits M x (upd M o x oo) with hNew
  have hnew : ∀ id, id ∈ Seen → id ∉ New := by
    intro id hs hn
    cases id with
    | init a b k => exact init_not_mem_newUnits hn
    | new ν k =>
      obtain ⟨x', ν⟩ := ν
      obtain ⟨h, -⟩ := new_mem_newUnits.1 hn
      simp only at h
      subst h
      exact hSeen ν k hs
  rw [mem_contents_iff] at hy
  have key : ∀ z ∈ Common (none : UW ub) New, ∀ (a : Fin (A + A')) (ν : (M.kind x).Cn) k,
      Holds (hold0 M.np) (hold1 M.np) a (Uid.new ⟨x, ν⟩ k : Uid A U0 M.N U1) →
      ext (hold0 M.np) (hold1 M.np) New y z a (.new ⟨x, ν⟩ k) = z (.new ⟨x, ν⟩ k) := by
    intro z hz a ν k ha
    rw [mem_common_iff] at hz
    by_cases hn : (Uid.new ⟨x, ν⟩ k : Uid A U0 M.N U1) ∈ New
    · exact ext_self hn ha
    · rw [ext_of_not hn, hz _ hn]
      exact hy _ _ fun hh => hSeen _ _ hh.1
  have hext : ∀ (z : Uid A U0 M.N U1 → UW ub) p, ∀ e, ∀ id ∈ ids e,
      ext (hold0 M.np) (hold1 M.np) New y z (M.part x p) id = y (M.part x p) id := fun z p e id hid =>
    ext_of_not (hnew id (hids e id hid))
  have e1 : ∀ z ∈ Common (none : UW ub) New, ∀ p,
      role M x p t (fun e => ids e.1) (upd M o x oo) (ext (hold0 M.np) (hold1 M.np) New y z (M.part x p)) =
      codeTab (M.kind x).c (M.kind x).d (chCode (M.kind x) ub U1 (t * ub)) p (outTab (M.kind x) ub X oo p)
        (fun ν k => z (.new ⟨x, ν⟩ k)) := by
    intro z hz p
    have hoo : (fun ν => upd M o x oo ⟨x, ν⟩) = oo := funext fun ν => upd_self o x oo ν
    rw [role_eq_codeTab (X := X), hoo]
    · exact codeTab_congr _ _ _ fun ν hν => funext fun k => key z hz _ _ _ (holds_new hν k)
    · intro e id hid
      rw [hext z p e.1 id hid]
      obtain ⟨e, he⟩ := e
      rcases he with he | he
      · rw [← he]; exact (hne e id hid).1
      · rw [← he]; exact (hne e id hid).2
    · intro k e
      rw [hX]
      simp only
      rw [slotBits_congr (hext z p e.1)]
  rw [Finset.sum_congr rfl fun z hz => Finset.prod_congr rfl fun p _ => e1 z hz p]
  refine Finset.sum_bij_ne_zero (fun z _ _ => fun ν k => z (.new ⟨x, ν⟩ k)) ?_ ?_ ?_ ?_
  · exact fun _ _ _ => Finset.mem_univ _
  · intro z1 h1 _ z2 h2 _ heq
    rw [mem_common_iff] at h1 h2
    funext id
    by_cases hn : id ∈ New
    · cases id with
      | init a b k => exact absurd hn init_not_mem_newUnits
      | new ν k =>
        obtain ⟨x', ν⟩ := ν
        obtain ⟨h, -⟩ := new_mem_newUnits.1 hn
        simp only at h
        subst h
        exact congrFun (congrFun heq ν) k
    · rw [h1 _ hn, h2 _ hn]
  · intro ζ _ hζ
    have hζ' : ∀ p, codeTab (M.kind x).c (M.kind x).d (chCode (M.kind x) ub U1 (t * ub)) p
        (outTab (M.kind x) ub X oo p) ζ ≠ 0 := fun p h0 => hζ (Finset.prod_eq_zero (Finset.mem_univ p) h0)
    let z : Uid A U0 M.N U1 → UW ub := fun id => match id with
      | .init _ _ _ => none
      | .new ν k => if h : x = ν.1 then (h ▸ ζ : (M.kind ν.1).Cn → Fin U1 → UW ub) ν.2 k else none
    have hz : ∀ ν k, z (.new ⟨x, ν⟩ k) = ζ ν k := fun ν k => by simp [z]
    refine ⟨z, ?_, ?_, ?_⟩
    · rw [mem_common_iff]
      intro id hn
      cases id with
      | init a b k => rfl
      | new ν k =>
        obtain ⟨x', ν⟩ := ν
        by_cases hx : x = x'
        · subst hx
          rw [hz]
          rw [hNew, new_mem_newUnits] at hn
          simp only [true_and, not_le, upd_self] at hn
          obtain ⟨i, -, h1⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hζ' ((M.kind x).c ν))
          obtain ⟨g, -, h2⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
          split_ifs at h2 with h3
          swap
          · exact absurd rfl h2
          have h4 := h3 ⟨ν, Or.inl rfl⟩
          rw [outTab] at h2
          split_ifs at h2 with h5
          swap
          · exact absurd rfl h2
          have h6 := h5 ⟨ν, Or.inl rfl⟩
          rw [← h4]
          show unitsOf ub _ _ = none
          rw [unitsOf_eq_none, h6]
          exact hn
        · simp only [z]
          rw [dif_neg hx]
    · simpa only [hz] using hζ
    · funext ν k
      exact hz ν k
  · intro z _ _
    rfl

/-- **The identity of one move.** -/
theorem move_identity (hub : 0 < ub) (x : Fin E) {m t : ℕ} (hm : (M.kind x).Le m)
    (hB : t * ub * (m + (M.kind x).lam) / ub + 1 ≤ U1) (o : M.N → Fin U1) (Seen : Finset (Uid A U0 M.N U1))
    (hSeen : ∀ (ν : (M.kind x).Cn) k, Uid.new ⟨x, ν⟩ k ∉ Seen)
    {y : Fin (A + A') → Uid A U0 M.N U1 → UW ub} (hy : y ∈ Contents (hold0 M.np) (hold1 M.np) none Seen)
    (ids : (M.kind x).Sl → List (Uid A U0 M.N U1)) (hids : ∀ e, ∀ id ∈ ids e, id ∈ Seen) (ht : ∀ e, (ids e).length ≤ t)
    (hne : ∀ e, ∀ id ∈ ids e, y (M.part x ((M.kind x).a e)) id ≠ none ∧ y (M.part x ((M.kind x).b e)) id ≠ none) :
    (∑ oo : (M.kind x).Cn → Fin U1, ∑ z ∈ Common none (newUnits M x (upd M o x oo)), ∏ p,
      role M x p t (fun e => ids e.1) (upd M o x oo)
        (ext (hold0 M.np) (hold1 M.np) (newUnits M x (upd M o x oo)) y z (M.part x p))) =
      if ∀ e, ∀ id ∈ ids e, y (M.part x ((M.kind x).a e)) id = y (M.part x ((M.kind x).b e)) id then 1 else 0 := by
  classical
  rw [Finset.sum_congr rfl fun oo _ => move_outcome x o Seen hSeen hy ids hids ht hne oo, sum_outTab hub hm hB]
  by_cases hall : ∀ e, ∀ id ∈ ids e, y (M.part x ((M.kind x).a e)) id = y (M.part x ((M.kind x).b e)) id
  · rw [if_pos hall, if_pos]
    exact fun e => (slotBits_eq_iff (fun id hid => (hne e id hid).1) (fun id hid => (hne e id hid).2) (ht e)).2 (hall e)
  · rw [if_neg hall, if_neg]
    exact fun h => hall fun e =>
      (slotBits_eq_iff (fun id hid => (hne e id hid).1) (fun id hid => (hne e id hid).2) (ht e)).1 (h e)

/-- Impossible outcomes of a move contribute nothing. -/
theorem move_zero (hub : 0 < ub) (x : Fin E) {m t : ℕ} (hm : (M.kind x).Le m)
    (hB : t * ub * (m + (M.kind x).lam) / ub + 1 ≤ U1) (o : M.N → Fin U1) (Seen : Finset (Uid A U0 M.N U1))
    (hSeen : ∀ (ν : (M.kind x).Cn) k, Uid.new ⟨x, ν⟩ k ∉ Seen)
    {y : Fin (A + A') → Uid A U0 M.N U1 → UW ub} (hy : y ∈ Contents (hold0 M.np) (hold1 M.np) none Seen)
    (ids : (M.kind x).Sl → List (Uid A U0 M.N U1)) (hids : ∀ e, ∀ id ∈ ids e, id ∈ Seen) (ht : ∀ e, (ids e).length ≤ t)
    (hne : ∀ e, ∀ id ∈ ids e, y (M.part x ((M.kind x).a e)) id ≠ none ∧ y (M.part x ((M.kind x).b e)) id ≠ none)
    (oo : (M.kind x).Cn → Fin U1)
    (hoo : ¬ ∃ i : Fin (t * ub) → (M.kind x).I, ∀ ν, (oo ν).1 = (∑ k, ((M.kind x).lam + (M.kind x).len (i k) ν)) / ub) :
    (∑ z ∈ Common none (newUnits M x (upd M o x oo)), ∏ p,
      role M x p t (fun e => ids e.1) (upd M o x oo)
        (ext (hold0 M.np) (hold1 M.np) (newUnits M x (upd M o x oo)) y z (M.part x p))) = 0 := by
  rw [move_outcome x o Seen hSeen hy ids hids ht hne oo]
  exact sum_codeTab_zero hub hm hB _ oo hoo

end Identity

end Nc.G
