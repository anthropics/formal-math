/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.G.Move

/-!
# The play, for general laws
-/

set_option linter.unusedSectionVars false

namespace Nc.G

open Finset Nc.Cut

variable {F : Type} [CommRing F] {A A' E U0 U1 ub : ℕ} {M : Sys F (A + A') E}

theorem init_mem_seen0 {N : Type} [Fintype N] [DecidableEq N] {n : Fin A → Fin A → Fin (U0 + 1)} {a b : Fin A}
    {k : Fin U0} : (Uid.init a b k : Uid A U0 N U1) ∈ seen0 n ↔ k.1 < (n a b).1 := by
  simp [seen0]

theorem new_not_mem_seen0 {N : Type} [Fintype N] [DecidableEq N] {n : Fin A → Fin A → Fin (U0 + 1)} {ν : N}
    {k : Fin U1} : (Uid.new ν k : Uid A U0 N U1) ∉ seen0 n := by
  simp [seen0]

namespace Plan

variable {P : Plan M U0 U1} {n : Fin A → Fin A → Fin (U0 + 1)} {o o' : M.N → Fin U1}

theorem mem_seenAt {x : ℕ} {id : Uid A U0 M.N U1} : id ∈ seenAt n o x ↔
    id ∈ seen0 n ∨ ∃ x' : Fin E, x'.1 < x ∧ id ∈ newUnits M x' o := by
  simp [seenAt]

theorem new_mem_seenAt {x : ℕ} {ν : M.N} {k : Fin U1} :
    (Uid.new ν k : Uid A U0 M.N U1) ∈ seenAt n o x ↔ ν.1.1 < x ∧ k ≤ o ν := by
  rw [mem_seenAt]
  constructor
  · rintro (h | ⟨x', hx', h⟩)
    · exact absurd h new_not_mem_seen0
    · obtain ⟨rfl, h2⟩ := new_mem_newUnits.1 h
      exact ⟨hx', h2⟩
  · rintro ⟨h1, h2⟩
    exact Or.inr ⟨ν.1, h1, new_mem_newUnits.2 ⟨rfl, h2⟩⟩

theorem init_mem_seenAt {x : ℕ} {a b : Fin A} {k : Fin U0} :
    (Uid.init a b k : Uid A U0 M.N U1) ∈ seenAt n o x ↔ k.1 < (n a b).1 := by
  rw [mem_seenAt, init_mem_seen0]
  refine or_iff_left ?_
  rintro ⟨x', -, h⟩
  exact init_not_mem_newUnits h

/-- The units seen in the end. -/
theorem mem_seenAt_end {id : Uid A U0 M.N U1} : id ∈ seenAt n o E ↔ unum id < ucnt n o id := by
  cases id with
  | init a b k => exact init_mem_seenAt
  | new ν k =>
    rw [new_mem_seenAt]
    simp only [unum, ucnt, Nat.lt_succ_iff, ν.1.2, true_and]
    exact Iff.rfl

theorem mem_used {x : ℕ} {id : Uid A U0 M.N U1} : id ∈ P.used n o x ↔ ∃ z : M.Z, z.1.1 < x ∧ id ∈ P.cons n o z := by
  simp [used]

theorem mem_cur {x : ℕ} {id : Uid A U0 M.N U1} : id ∈ P.cur n o x ↔ id ∈ seenAt n o x ∧
    ∀ z : M.Z, z.1.1 < x → id ∉ P.cons n o z := by
  rw [cur, Finset.mem_sdiff, mem_used]
  push Not
  exact Iff.rfl

theorem mem_ids {z : M.Z} {id : Uid A U0 M.N U1} : id ∈ P.ids n o z ↔ id ∈ P.cons n o z := by
  simp [ids, allIds]

theorem length_ids {z : M.Z} : (P.ids n o z).length = (P.cons n o z).card := by
  rw [← List.toFinset_card_of_nodup]
  · congr 1
    ext id
    rw [List.mem_toFinset, mem_ids]
  · exact (Finset.nodup_toList _).filter _

theorem ids_congr {z : M.Z} (h : P.cons n o z = P.cons n o' z) : P.ids n o z = P.ids n o' z := by
  simp only [ids, h]

end Plan

section Lemmas

variable {P : Plan M U0 U1} {cap : ℕ} {n : Fin A → Fin A → Fin (U0 + 1)} {o o' : M.N → Fin U1}

theorem holds_cons (hP : P.Ok cap) {x : Fin E} {p : (M.kind x).Ro} {e : (M.kind x).Sl}
    (he : (M.kind x).a e = p ∨ (M.kind x).b e = p) {id : Uid A U0 M.N U1} (h : id ∈ P.cons n o ⟨x, e⟩) :
    Holds (hold0 M.np) (hold1 M.np) (M.part x p) id := by
  have h1 : (hold0 M.np id = M.part x ((M.kind x).a e) ∧ hold1 M.np id = M.part x ((M.kind x).b e)) ∨
      (hold1 M.np id = M.part x ((M.kind x).a e) ∧ hold0 M.np id = M.part x ((M.kind x).b e)) :=
    hP.hold n o ⟨x, e⟩ id h
  rcases he with rfl | rfl <;> rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl h1.symm
  · exact Or.inr h1.symm
  · exact Or.inr h2.symm
  · exact Or.inl h2.symm

theorem seenAt_congr {x : ℕ} (h : ∀ ν : M.N, ν.1.1 < x → o ν = o' ν) :
    (Plan.seenAt n o x : Finset (Uid A U0 M.N U1)) = Plan.seenAt n o' x := by
  ext id
  cases id with
  | init a b k => rw [Plan.init_mem_seenAt, Plan.init_mem_seenAt]
  | new ν k =>
    rw [Plan.new_mem_seenAt, Plan.new_mem_seenAt]
    exact and_congr_right fun hx => by rw [h ν hx]

theorem cons_congr (hP : P.Ok cap) {x : ℕ} (h : ∀ ν : M.N, ν.1.1 < x → o ν = o' ν) (z : M.Z) (hz : z.1.1 ≤ x) :
    P.cons n o z = P.cons n o' z :=
  hP.causal n o o' z fun ν hν => h ν (lt_of_lt_of_le hν hz)

theorem num_congr (hP : P.Ok cap) {x : ℕ} (h : ∀ ν : M.N, ν.1.1 < x → o ν = o' ν) (x' : Fin E) (hx' : x'.1 ≤ x) :
    P.num n o x' = P.num n o' x' :=
  hP.causal' n o o' x' fun ν hν => h ν (lt_of_lt_of_le hν hx')

theorem cur_congr (hP : P.Ok cap) {x : ℕ} (h : ∀ ν : M.N, ν.1.1 < x → o ν = o' ν) : P.cur n o x = P.cur n o' x := by
  ext id
  rw [Plan.mem_cur, Plan.mem_cur, seenAt_congr h]
  exact and_congr_right fun _ => forall_congr' fun z => imp_congr_right fun hz => by
    rw [cons_congr hP h z hz.le]

theorem roleAt_congr_o (hP : P.Ok cap) {x : Fin E} (h : ∀ ν : M.N, ν.1.1 < x.1 → o ν = o' ν)
    (ho : ∀ ν, o ⟨x, ν⟩ = o' ⟨x, ν⟩) (p : (M.kind x).Ro) (y : Uid A U0 M.N U1 → UW ub) :
    roleAt P n o ⟨x, p⟩ y = roleAt P n o' ⟨x, p⟩ y := by
  unfold roleAt
  have e1 : P.num n o x = P.num n o' x := num_congr hP h x le_rfl
  have e2 : (fun e : (M.kind x).SlAt p => P.ids n o ⟨x, e.1⟩) = fun e => P.ids n o' ⟨x, e.1⟩ :=
    funext fun e => Plan.ids_congr (cons_congr hP h ⟨x, e.1⟩ le_rfl)
  simp only [e1, e2]
  exact role_congr ho (fun _ _ _ => rfl) fun _ _ => rfl

/-- The joint weight before move `x`. -/
noncomputable def tabUpTo (P : Plan M U0 U1) (n : Fin A → Fin A → Fin (U0 + 1)) (o : M.N → Fin U1)
    (init : Fin (A + A') → (Uid A U0 M.N U1 → UW ub) → F) (x : ℕ) (y : Fin (A + A') → Uid A U0 M.N U1 → UW ub) : F :=
  (∏ a, init a (y a)) * ∏ x' ∈ univ.filter (fun x' : Fin E => x'.1 < x), ∏ p, roleAt P n o ⟨x', p⟩ (y (M.part x' p))

variable {init : Fin (A + A') → (Uid A U0 M.N U1 → UW ub) → F}

/-- Units that are present if the joint weight is not zero. -/
theorem tabUpTo_ne_none {x : ℕ} {y : Fin (A + A') → Uid A U0 M.N U1 → UW ub}
    (hinit : ∀ a y, init a y ≠ 0 → ∀ id ∈ seen0 (N := M.N) (U1 := U1) n, Holds (hold0 M.np) (hold1 M.np) a id →
      y id ≠ none) (h : tabUpTo P n o init x y ≠ 0) {a : Fin (A + A')} {id : Uid A U0 M.N U1}
    (hid : id ∈ Plan.seenAt n o x) (ha : Holds (hold0 M.np) (hold1 M.np) a id) : y a id ≠ none := by
  have h1 := left_ne_zero_of_mul h
  have h2 := right_ne_zero_of_mul h
  cases id with
  | init b c k =>
    have h3 : init a (y a) ≠ 0 := fun h0 => h1 (Finset.prod_eq_zero (Finset.mem_univ a) h0)
    exact hinit a _ h3 _ (init_mem_seen0.2 (Plan.init_mem_seenAt.1 hid)) ha
  | new ν k =>
    obtain ⟨hx, hk⟩ := Plan.new_mem_seenAt.1 hid
    obtain ⟨x', ν⟩ := ν
    have h3 : ∀ p, roleAt P n o ⟨x', p⟩ (y (M.part x' p)) ≠ 0 := by
      intro p h0
      exact h2 (Finset.prod_eq_zero (Finset.mem_filter.2 ⟨Finset.mem_univ x', hx⟩)
        (Finset.prod_eq_zero (Finset.mem_univ p) h0))
    rcases ha with ha | ha
    · have : a = M.part x' ((M.kind x').c ν) := ha
      rw [this]
      exact role_new_ne_none (h3 ((M.kind x').c ν)) (Or.inl rfl) hk
    · have : a = M.part x' ((M.kind x').d ν) := ha
      rw [this]
      exact role_new_ne_none (h3 ((M.kind x').d ν)) (Or.inr rfl) hk

/-- The joint weight before move `x` does not depend on the copies of later units. -/
theorem tabUpTo_congr (hP : P.Ok cap)
    (hloc : ∀ a y y', (∀ b c k, y (.init b c k) = y' (.init b c k)) → init a y = init a y') {x : ℕ}
    {y y' : Fin (A + A') → Uid A U0 M.N U1 → UW ub} (h1 : ∀ a b c k, y a (.init b c k) = y' a (.init b c k))
    (h2 : ∀ a (ν : M.N) k, ν.1.1 < x → y a (.new ν k) = y' a (.new ν k)) :
    tabUpTo P n o init x y = tabUpTo P n o init x y' := by
  unfold tabUpTo
  congr 1
  · exact Finset.prod_congr rfl fun a _ => hloc a _ _ (h1 a)
  · refine Finset.prod_congr rfl fun x' hx' => Finset.prod_congr rfl fun p _ => ?_
    have hx := (Finset.mem_filter.1 hx').2
    refine role_congr (fun _ => rfl) (fun e id hid => ?_) fun ν k => h2 _ _ _ hx
    have hs := (Plan.mem_cur.1 (hP.sub n o _ (Plan.mem_ids.1 hid))).1
    cases id with
    | init a b k => exact h1 _ _ _ _
    | new ν k => exact h2 _ _ _ ((Plan.new_mem_seenAt.1 hs).1.trans hx)

theorem tabUpTo_congr_o (hP : P.Ok cap) {x : ℕ} (h : ∀ ν : M.N, ν.1.1 < x → o ν = o' ν)
    (y : Fin (A + A') → Uid A U0 M.N U1 → UW ub) : tabUpTo P n o init x y = tabUpTo P n o' init x y := by
  unfold tabUpTo
  congr 1
  refine Finset.prod_congr rfl fun x' hx' => Finset.prod_congr rfl fun p _ => ?_
  have hx := (Finset.mem_filter.1 hx').2
  exact roleAt_congr_o hP (fun ν hν => h ν (hν.trans hx)) (fun ν => h ⟨x', ν⟩ hx) p _

theorem filter_lt_succ (x : Fin E) : univ.filter (fun x' : Fin E => x'.1 < x.1 + 1) =
    insert x (univ.filter fun x' : Fin E => x'.1 < x.1) := by
  ext x'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
  omega

theorem tabUpTo_succ (x : Fin E) (y : Fin (A + A') → Uid A U0 M.N U1 → UW ub) :
    tabUpTo P n o init (x.1 + 1) y = tabUpTo P n o init x.1 y * ∏ p, roleAt P n o ⟨x, p⟩ (y (M.part x p)) := by
  unfold tabUpTo
  rw [filter_lt_succ, Finset.prod_insert (by simp)]
  ring

theorem seenAt_succ (x : Fin E) :
    (Plan.seenAt n o (x.1 + 1) : Finset (Uid A U0 M.N U1)) = Plan.seenAt n o x.1 ∪ newUnits M x o := by
  ext id
  rw [Finset.mem_union]
  cases id with
  | init a b k =>
    rw [Plan.init_mem_seenAt, Plan.init_mem_seenAt]
    exact (or_iff_left init_not_mem_newUnits).symm
  | new ν k =>
    rw [Plan.new_mem_seenAt, Plan.new_mem_seenAt, new_mem_newUnits, Fin.ext_iff]
    constructor
    · rintro ⟨h1, h2⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h | h
      · exact Or.inl ⟨h, h2⟩
      · exact Or.inr ⟨h, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨Nat.lt_succ_of_lt h1, h2⟩
      · exact ⟨by omega, h2⟩

/-- The units given in a move. -/
def outSet (P : Plan M U0 U1) (n : Fin A → Fin A → Fin (U0 + 1)) (o : M.N → Fin U1) (x : Fin E) :
    Finset (Uid A U0 M.N U1) := univ.biUnion fun e : (M.kind x).Sl => P.cons n o ⟨x, e⟩

theorem mem_outSet {x : Fin E} {id : Uid A U0 M.N U1} : id ∈ outSet P n o x ↔ ∃ e, id ∈ P.cons n o ⟨x, e⟩ := by
  simp [outSet]

theorem cur_succ (hP : P.Ok cap) (x : Fin E) :
    P.cur n o (x.1 + 1) = (P.cur n o x.1 \ outSet P n o x) ∪ newUnits M x o := by
  ext id
  rw [Finset.mem_union, Finset.mem_sdiff, Plan.mem_cur, Plan.mem_cur, seenAt_succ, Finset.mem_union, mem_outSet]
  constructor
  · rintro ⟨h1 | h1, h2⟩
    · refine Or.inl ⟨⟨h1, fun z hz => h2 z (Nat.lt_succ_of_lt hz)⟩, ?_⟩
      rintro ⟨e, he⟩
      exact h2 ⟨x, e⟩ (Nat.lt_succ_self _) he
    · exact Or.inr h1
  · rintro (⟨⟨h1, h2⟩, h3⟩ | h)
    · refine ⟨Or.inl h1, fun z hz hc => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hz with h4 | h4
      · exact h2 z h4 hc
      · obtain ⟨x', e⟩ := z
        have : x' = x := Fin.ext h4
        subst this
        exact h3 ⟨e, hc⟩
    · refine ⟨Or.inr h, fun z hz hc => ?_⟩
      have hs := (Plan.mem_cur.1 (hP.sub n o z hc)).1
      cases id with
      | init a b k => exact init_not_mem_newUnits h
      | new ν k =>
        have h1 := (new_mem_newUnits.1 h).1
        have h2 := (Plan.new_mem_seenAt.1 hs).1
        rw [h1] at h2
        omega

end Lemmas

open Classical in
/-- **Paper: Units.** "Each choice of indices and bits occurs for exactly one outcome, so the value does not change":
one move, as a sum over outcomes that are good. -/
theorem _root_.Paper.thm_tree_move {P : Plan M U0 U1} {cap : ℕ} (hP : P.Ok cap) (hub : 0 < ub)
    (hgood : ∀ n o x, P.Poss n o ub x → P.good n o x) {m : Fin E → ℕ}
    (hm : ∀ x, (M.kind x).Le (m x)) (hU1 : ∀ x, cap * (m x + (M.kind x).lam) + 1 ≤ U1)
    {n : Fin A → Fin A → Fin (U0 + 1)} {o : M.N → Fin U1} (x : Fin E) {y : Fin (A + A') → Uid A U0 M.N U1 → UW ub}
    (hy : y ∈ Contents (hold0 M.np) (hold1 M.np) none (Plan.seenAt n o x.1))
    (hne : ∀ a id, id ∈ Plan.seenAt n o x.1 → Holds (hold0 M.np) (hold1 M.np) a id → y a id ≠ none) :
    (if Agree (hold0 M.np) (hold1 M.np) (outSet P n o x) y then (1 : F) else 0) =
      ∑ oo : (M.kind x).Cn → Fin U1, ∑ z ∈ Common none (newUnits M x (upd M o x oo)),
        if P.good n (upd M o x oo) x then ∏ p,
        role M x p (P.num n o x) (fun e => P.ids n o ⟨x, e.1⟩) (upd M o x oo)
          (ext (hold0 M.np) (hold1 M.np) (newUnits M x (upd M o x oo)) y z (M.part x p)) else 0 := by
  have hnumo : ∀ oo : (M.kind x).Cn → Fin U1, P.num n (upd M o x oo) x = P.num n o x := fun oo =>
    hP.causal' n _ o x fun ν hν => upd_ne _ _ (ne_of_lt hν)
  have hB : P.num n o x * ub * (m x + (M.kind x).lam) / ub + 1 ≤ U1 := by
    refine le_trans ?_ (hU1 x)
    rw [mul_assoc, mul_comm ub, ← mul_assoc, Nat.mul_div_cancel _ hub]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (hP.cap n o x)) 1
  have hseen : ∀ e, ∀ id ∈ P.ids n o ⟨x, e⟩, id ∈ Plan.seenAt n o x.1 := fun e id hid =>
    (Plan.mem_cur.1 (hP.sub n o ⟨x, e⟩ (Plan.mem_ids.1 hid))).1
  have hSeen : ∀ (ν : (M.kind x).Cn) (k : Fin U1), (Uid.new ⟨x, ν⟩ k : Uid A U0 M.N U1) ∉ Plan.seenAt n o x.1 :=
    fun ν k h => lt_irrefl _ (Plan.new_mem_seenAt.1 h).1
  have hlen : ∀ e, (P.ids n o ⟨x, e⟩).length ≤ P.num n o x := fun e => by
    rw [Plan.length_ids]
    exact hP.card n o ⟨x, e⟩
  have hne' : ∀ e, ∀ id ∈ P.ids n o ⟨x, e⟩, y (M.part x ((M.kind x).a e)) id ≠ none ∧
      y (M.part x ((M.kind x).b e)) id ≠ none := fun e id hid =>
    ⟨hne _ _ (hseen e id hid) (holds_cons hP (Or.inl rfl) (Plan.mem_ids.1 hid)),
      hne _ _ (hseen e id hid) (holds_cons hP (Or.inr rfl) (Plan.mem_ids.1 hid))⟩
  have hz : ∀ oo : (M.kind x).Cn → Fin U1, (∑ z ∈ Common none (newUnits M x (upd M o x oo)),
      if P.good n (upd M o x oo) x then ∏ p,
        role M x p (P.num n o x) (fun e => P.ids n o ⟨x, e.1⟩) (upd M o x oo)
          (ext (hold0 M.np) (hold1 M.np) (newUnits M x (upd M o x oo)) y z (M.part x p)) else (0 : F)) =
      ∑ z ∈ Common none (newUnits M x (upd M o x oo)), ∏ p,
        role M x p (P.num n o x) (fun e => P.ids n o ⟨x, e.1⟩) (upd M o x oo)
          (ext (hold0 M.np) (hold1 M.np) (newUnits M x (upd M o x oo)) y z (M.part x p)) := by
    intro oo
    by_cases hg : P.good n (upd M o x oo) x
    · simp only [hg, if_true]
    · simp only [hg, if_false, Finset.sum_const_zero]
      symm
      refine move_zero hub x (hm x) hB o (Plan.seenAt n o x.1) hSeen hy (fun e => P.ids n o ⟨x, e⟩) hseen hlen hne' oo ?_
      rintro ⟨i, hi⟩
      refine hg (hgood n _ x ?_)
      have e1 := hnumo oo
      unfold Plan.Poss
      rw [e1]
      exact ⟨i, fun ν => by rw [upd_self]; exact hi ν⟩
  rw [Finset.sum_congr rfl fun oo _ => hz oo]
  rw [move_identity hub x (hm x) (t := P.num n o x) hB o (Plan.seenAt n o x.1) hSeen hy
    (fun e => P.ids n o ⟨x, e⟩) hseen hlen hne']
  · refine if_congr ⟨fun h e id hid => ?_, fun h id hid => ?_⟩ rfl rfl
    · have hid' := Plan.mem_ids.1 hid
      have ha := h id (mem_outSet.2 ⟨e, hid'⟩)
      rcases hP.hold n o ⟨x, e⟩ id hid' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2] at ha; exact ha
      · rw [h1, h2] at ha; exact ha.symm
    · obtain ⟨e, he⟩ := mem_outSet.1 hid
      have := h e id (Plan.mem_ids.2 he)
      rcases hP.hold n o ⟨x, e⟩ id he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2]; exact this
      · rw [h1, h2]; exact this.symm

theorem upd_upd (o : M.N → Fin U1) (x : Fin E) (oo oo' : (M.kind x).Cn → Fin U1) :
    upd M (upd M o x oo) x oo' = upd M o x oo' := by
  funext ν
  obtain ⟨x', ν⟩ := ν
  by_cases h : x' = x
  · subst h
    rw [upd_self, upd_self]
  · rw [upd_ne _ _ h, upd_ne _ _ h, upd_ne _ _ h]

theorem upd_eq_self (o : M.N → Fin U1) (x : Fin E) : upd M o x (fun ν => o ⟨x, ν⟩) = o := by
  funext ν
  obtain ⟨x', ν⟩ := ν
  by_cases h : x' = x
  · subst h
    rw [upd_self]
  · rw [upd_ne _ _ h]

open Classical in
/-- **Paper: Units.** "Every possible outcome is good ...; so the sum may be restricted to good outcomes": a whole plan
of moves keeps the value. -/
theorem _root_.Paper.thm_tree_moves {P : Plan M U0 U1} {cap : ℕ} (hP : P.Ok cap) (hub : 0 < ub)
    (hgood : ∀ n o x, P.Poss n o ub x → P.good n o x) {m : Fin E → ℕ}
    (hm : ∀ x, (M.kind x).Le (m x)) (hU : 0 < U1) (hU1 : ∀ x, cap * (m x + (M.kind x).lam) + 1 ≤ U1)
    (n : Fin A → Fin A → Fin (U0 + 1)) (init : Fin (A + A') → (Uid A U0 M.N U1 → UW ub) → F)
    (hloc : ∀ a y y', (∀ b c k, y (.init b c k) = y' (.init b c k)) → init a y = init a y')
    (hinit : ∀ a y, init a y ≠ 0 → ∀ id ∈ seen0 (N := M.N) (U1 := U1) n, Holds (hold0 M.np) (hold1 M.np) a id →
      y id ≠ none) :
    posVal (hold0 M.np) (hold1 M.np) (none : UW ub) (seen0 n) (seen0 n) (fun y => ∏ a, init a (y a)) =
      ∑ o : M.N → Fin U1, if ∀ x, P.good n o x then
        posVal (hold0 M.np) (hold1 M.np) none (Plan.seenAt n o E) (P.cur n o E) fun y =>
          ∏ a, partyTab P n o (init a) a (y a) else 0 := by
  let d : Fin U1 := ⟨0, hU⟩
  let pre : ℕ → Finset (M.N → Fin U1) := fun x => univ.filter fun o => ∀ ν : M.N, x ≤ ν.1.1 → o ν = d
  have claim : ∀ x, x ≤ E → posVal (hold0 M.np) (hold1 M.np) (none : UW ub) (seen0 n) (seen0 n)
      (fun y => ∏ a, init a (y a)) = ∑ o ∈ pre x, if ∀ x' : Fin E, x'.1 < x → P.good n o x' then
        posVal (hold0 M.np) (hold1 M.np) none
        (Plan.seenAt n o x) (P.cur n o x) (tabUpTo P n o init x) else 0 := by
    intro x
    induction x with
    | zero =>
      intro _
      have e1 : pre 0 = {fun _ => d} := by
        ext o
        simp only [pre, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · exact fun h => funext fun ν => h ν (Nat.zero_le _)
        · rintro rfl ν _; rfl
      rw [e1, Finset.sum_singleton]
      have e2 : (Plan.seenAt n (fun _ : M.N => d) 0 : Finset (Uid A U0 M.N U1)) = seen0 n := by
        ext id; simp [Plan.mem_seenAt]
      have e3 : P.cur n (fun _ : M.N => d) 0 = seen0 n := by
        ext id; simp [Plan.mem_cur, e2]
      have e4 : tabUpTo P n (fun _ => d) init 0 = fun y => ∏ a, init a (y a) := by
        funext y
        simp [tabUpTo]
      rw [e2, e3, e4, if_pos fun x' hx' => absurd hx' (Nat.not_lt_zero _)]
    | succ x ih =>
      intro hx
      rw [ih (Nat.le_of_succ_le hx)]
      let xE : Fin E := ⟨x, hx⟩
      have step : ∀ o ∈ pre x, (if ∀ x' : Fin E, x'.1 < x → P.good n o x' then
          posVal (hold0 M.np) (hold1 M.np) none (Plan.seenAt n o x) (P.cur n o x)
          (tabUpTo P n o init x) else 0) = ∑ oo : (M.kind xE).Cn → Fin U1,
          if ∀ x' : Fin E, x'.1 < x + 1 → P.good n (upd M o xE oo) x' then posVal (hold0 M.np) (hold1 M.np) none
          (Plan.seenAt n (upd M o xE oo) (x + 1)) (P.cur n (upd M o xE oo) (x + 1))
          (tabUpTo P n (upd M o xE oo) init (x + 1)) else 0 := by
        intro o _
        have hgx : ∀ (oo : (M.kind xE).Cn → Fin U1), (∀ x' : Fin E, x'.1 < x + 1 → P.good n (upd M o xE oo) x') ↔
            (∀ x' : Fin E, x'.1 < x → P.good n o x') ∧ P.good n (upd M o xE oo) xE := by
          intro oo
          have hc : ∀ x' : Fin E, x'.1 < x → (P.good n (upd M o xE oo) x' ↔ P.good n o x') := fun x' hx' =>
            hP.causal'' n _ o x' fun ν hν => upd_ne _ _ (by
              rintro h
              rw [h] at hν
              have : x ≤ x'.1 := hν
              omega)
          constructor
          · intro h
            exact ⟨fun x' hx' => (hc x' hx').1 (h x' (Nat.lt_succ_of_lt hx')), h xE (Nat.lt_succ_self _)⟩
          · rintro ⟨h1, h2⟩ x' hx'
            rcases Nat.lt_succ_iff_lt_or_eq.1 hx' with h3 | h3
            · exact (hc x' h3).2 (h1 x' h3)
            · have : x' = xE := Fin.ext h3
              rw [this]
              exact h2
        by_cases hall : ∀ x' : Fin E, x'.1 < x → P.good n o x'
        swap
        · rw [if_neg hall]
          symm
          refine Finset.sum_eq_zero fun oo _ => if_neg fun h => hall ((hgx oo).1 h).1
        rw [if_pos hall]
        rw [posVal_move' (hold0 M.np) (hold1 M.np) none (Plan.seenAt n o x) (P.cur n o x)
          (outSet P n o xE) (fun id h => ?_)
          (fun id h => (Plan.mem_cur.1 h).1) (fun oo : (M.kind xE).Cn → Fin U1 => newUnits M xE (upd M o xE oo))
          (fun oo => ?_) (tabUpTo P n o init x) (fun oo y z => ?_)
          (fun oo y => if P.good n (upd M o xE oo) xE then
            ∏ p, role M xE p (P.num n o xE) (fun e => P.ids n o ⟨xE, e.1⟩) (upd M o xE oo)
            (y (M.part xE p)) else 0) (fun y hy h0 => ?_)]
        · refine Finset.sum_congr rfl fun oo _ => ?_
          by_cases hgo : P.good n (upd M o xE oo) xE
          swap
          · rw [if_neg fun h => hgo ((hgx oo).1 h).2]
            simp only [hgo, if_false, mul_zero, posVal, ite_self, Finset.sum_const_zero]
          rw [if_pos ((hgx oo).2 ⟨hall, hgo⟩)]
          simp only [hgo, if_true]
          set o' := upd M o xE oo with ho'
          have hlt : ∀ ν : M.N, ν.1.1 < xE.1 → o ν = o' ν := by
            intro ν hν
            rw [ho', upd_ne]
            rintro h
            rw [h] at hν
            exact lt_irrefl _ hν
          have f1 : Plan.seenAt n o' (x + 1) = Plan.seenAt n o x ∪ newUnits M xE o' := by
            rw [show x + 1 = xE.1 + 1 from rfl, seenAt_succ xE, seenAt_congr hlt]
          have f0 : outSet P n o xE = outSet P n o' xE := by
            unfold outSet
            congr 1
            funext e
            exact cons_congr hP hlt ⟨xE, e⟩ le_rfl
          have f2 : P.cur n o' (x + 1) = (P.cur n o x \ outSet P n o xE) ∪ newUnits M xE o' := by
            rw [show x + 1 = xE.1 + 1 from rfl, cur_succ hP xE, ← cur_congr hP hlt, f0]
          have f3 : tabUpTo P n o' init (x + 1) = fun y => tabUpTo P n o init x y *
              ∏ p, role M xE p (P.num n o xE) (fun e => P.ids n o ⟨xE, e.1⟩) o' (y (M.part xE p)) := by
            funext y
            rw [show x + 1 = xE.1 + 1 from rfl, tabUpTo_succ, ← tabUpTo_congr_o hP hlt]
            congr 1
            refine Finset.prod_congr rfl fun p _ => ?_
            have e1 : P.num n o xE = P.num n o' xE := num_congr hP hlt xE le_rfl
            have e2 : (fun e : (M.kind xE).SlAt p => P.ids n o ⟨xE, e.1⟩) = fun e => P.ids n o' ⟨xE, e.1⟩ :=
              funext fun e => Plan.ids_congr (cons_congr hP hlt ⟨xE, e.1⟩ le_rfl)
            rw [roleAt, e1, e2]
          rw [f1, f2, f3]
        · obtain ⟨e, he⟩ := mem_outSet.1 h
          exact hP.sub n o ⟨xE, e⟩ he
        · rw [Finset.disjoint_left]
          intro id h1 h2
          cases id with
          | init a b k => exact init_not_mem_newUnits h2
          | new ν k =>
            have a1 := (new_mem_newUnits.1 h2).1
            have a2 := (Plan.new_mem_seenAt.1 h1).1
            rw [a1] at a2
            exact lt_irrefl _ a2
        · refine tabUpTo_congr hP hloc (fun a b c k => ?_) fun a ν k hν => ?_
          · exact ext_of_not init_not_mem_newUnits
          · refine ext_of_not fun h => ?_
            have a1 := (new_mem_newUnits.1 h).1
            rw [a1] at hν
            exact lt_irrefl _ hν
        · exact Paper.thm_tree_move hP hub hgood hm hU1 xE hy fun a id hid ha => tabUpTo_ne_none hinit h0 hid ha
      rw [Finset.sum_congr rfl step, ← Finset.sum_product']
      refine Finset.sum_bij' (i := fun q _ => upd M q.1 xE q.2)
        (j := fun o _ => (upd M o xE fun _ => d, fun ν => o ⟨xE, ν⟩)) ?_ ?_ ?_ ?_ ?_
      · rintro ⟨o, oo⟩ h
        simp only [pre, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at h ⊢
        intro ν hν
        rw [upd_ne]
        · exact h ν (Nat.le_of_succ_le hν)
        · rintro h'
          rw [h'] at hν
          exact absurd hν (Nat.not_succ_le_self x)
      · intro o h
        simp only [pre, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at h ⊢
        intro ν hν
        obtain ⟨x', ν⟩ := ν
        by_cases e : x' = xE
        · subst e
          rw [upd_self]
        · rw [upd_ne _ _ e]
          exact h _ (lt_of_le_of_ne hν fun h => e (Fin.ext h.symm))
      · rintro ⟨o, oo⟩ h
        simp only [pre, Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and, and_true] at h
        ext1
        · simp only [upd_upd]
          have : (fun _ : (M.kind xE).Cn => d) = fun ν => o ⟨xE, ν⟩ := funext fun ν => (h ⟨xE, ν⟩ le_rfl).symm
          rw [this, upd_eq_self]
        · funext ν
          exact upd_self _ _ _ ν
      · intro o _
        simp only [upd_upd]
        exact upd_eq_self o xE
      · rintro ⟨o, oo⟩ _
        rfl
  rw [claim E le_rfl]
  have e1 : pre E = univ := by
    ext o
    simp only [pre, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact fun ν hν => absurd ν.1.2 (not_lt.2 hν)
  rw [e1]
  refine Finset.sum_congr rfl fun o _ => if_congr ⟨fun h x => h x x.2, fun h x _ => h x⟩ ?_ rfl
  congr 1
  funext y
  unfold tabUpTo partyTab
  rw [Finset.prod_mul_distrib]
  congr 1
  have e2 : univ.filter (fun x' : Fin E => x'.1 < E) = univ := by
    ext x'; simp
  rw [e2, ← Fintype.prod_sigma' (f := fun x' p => roleAt P n o ⟨x', p⟩ (y (M.part x' p)))]
  symm
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun r _ => ?_
  rw [Finset.prod_ite_eq, if_pos (Finset.mem_univ _)]
  rfl

end Nc.G
