/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Ok
import Nc.Tow.Load3
import Nc.Tow.Tree

/-!
# The tower plan: the units in the end
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b D J r m Uu AA A' U0 U1 : ℕ} {T : Tower h b D J r} {R : Routes T m Uu}
  {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {Pl : Place T ch A'} {lhat : ℕ}

/-- Relays that are targets exist. -/
theorem nxt_ok_R {x y : RM T m AA} (hx : okR T R ch x) {ν : Bool} (he : tgR T R ch x ν = .nxt y) :
    okR T R ch y ∧ inpR T y = .nxt y ∧ ∀ L : Tg T m AA → ℕ, ActR L y := by
  have hE : ∀ e : Option (T.Ed 0), (edgeO T e : Tg T m AA) ≠ .nxt y := by
    intro e he
    cases e <;> simp [edgeO] at he
  have mid : ∀ (j : Fin J) (e : T.Ed j) (s : Fin 4), s ≠ 0 → okR T R ch (.mid j e s) →
      okR T R ch (.mid j e s) ∧ inpR T (.mid j e s : RM T m AA) = .nxt (.mid j e s) ∧
        ∀ L : Tg T m AA → ℕ, ActR L (.mid j e s) := by
    intro j e s hs hok
    refine ⟨hok, ?_, fun L h0 => absurd h0 hs⟩
    rw [inpR_mid, if_neg hs]
  rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e
  · cases ν
    · exact absurd he (hE _)
    · simp only [tgR] at he
      split_ifs at he with hs
      · have he := Tg.nxt.inj he
        subst he
        exact ⟨⟨hx.1, hs.2⟩, rfl, fun _ => trivial⟩
      · exact absurd he (hE _)
  · simp [tgR] at he
  · cases ν
    · fin_cases s <;> simp [tgR] at he
    · fin_cases s
      · simp only [tgR, Fin.zero_eta, Matrix.cons_val_zero] at he
        split_ifs at he with hq
        · have he := Tg.nxt.inj he
          subst he
          exact mid j e 1 (by decide) ⟨fun _ => hq, fun h3 => absurd h3 (by decide)⟩
        · have he := Tg.nxt.inj he
          subst he
          exact mid j e 2 (by decide) ⟨fun h3 => absurd h3 (by decide), fun h3 => absurd h3 (by decide)⟩
      · simp only [tgR, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero] at he
        have he := Tg.nxt.inj he
        subst he
        exact mid j e 2 (by decide) ⟨fun h3 => absurd h3 (by decide), fun h3 => absurd h3 (by decide)⟩
      · simp only [tgR, Fin.reduceFinMk, Matrix.cons_val] at he
        split_ifs at he with hq
        have he := Tg.nxt.inj he
        subst he
        exact mid j e 3 (by decide) ⟨fun h3 => absurd h3 (by decide), fun _ => hq⟩
      · simp [tgR] at he
  · simp [tgR] at he

theorem nxt_ok_B {a c : Fin AA} {k : ℕ} {y : RM T m AA} (he : tgB T R ch a c k = .nxt y) :
    okR T R ch y ∧ inpR T y = .nxt y ∧ ∀ L : Tg T m AA → ℕ, ActR L y := by
  have hE : ∀ e : Option (T.Ed 0), (edgeO T e : Tg T m AA) ≠ .nxt y := by
    intro e he
    cases e <;> simp [edgeO] at he
  unfold tgB at he
  by_cases hac : a = c
  · rw [if_pos hac] at he
    cases he
  · rw [if_neg hac] at he
    by_cases hs : 0 < 2 * m ∧ 1 < R.pl (ch a) (ch c) (gam T ch a k)
    · rw [dif_pos hs] at he
      have he := Tg.nxt.inj he
      subst he
      exact ⟨⟨hac, hs.2⟩, rfl, fun _ => trivial⟩
    · rw [dif_neg hs] at he
      exact absurd he (hE _)

/-- End segments join different chambers. -/
theorem seg_nondiag (hr : 0 < r) (hb : 0 < b) {j : Fin J} {i : Fin h} {ω : T.V (j + 1) i} {q : Sym2 T.Fl}
    {ν : NM R FL (ch := ch)} (hν : tgM R ch FL ν.1 ν.2 = .seg j i ω q) : ¬ q.IsDiag := by
  have key : ∀ c : T.X j, T.host i (T.vx i c) ≠ T.π c → ¬ (s(T.co i (T.host i (T.vx i c)), T.co i c) : Sym2 T.Fl).IsDiag := by
    intro c hne hd
    rw [Sym2.mk_isDiag_iff] at hd
    apply hne
    apply (T.vx_co (Nat.succ_le_of_lt j.2) i).1
    refine Prod.ext ?_ ?_
    · simp only
      rw [T.host_vx j.2, T.π_vx j.2]
    · simp only
      rw [hd, T.π_co j.2]
  obtain ⟨e, s, hx, h1, -, h3⟩ := seg_chan hr hb hν
  subst h1
  rcases h3 with ⟨h5, -, h7⟩ | ⟨h5, -, h7⟩
  · subst h5
    rw [← h7]
    exact key _ (hx.1 rfl)
  · subst h5
    rw [← h7]
    exact key _ (hx.2 rfl).symm

section Plan

variable {n : Fin AA → Fin AA → Fin (U0 + 1)} {o : (sys R FL Pl).N → Fin U1}

/-- Alive units with a target are given. -/
theorem exists_cons (hr : 0 < r) (hb : 0 < b) (hh : 0 < h) {u : Un R FL Pl U0 U1} (hu : AlU R FL Pl lhat n o u)
    (hd : tgU R FL Pl u ≠ .done) : ∃ z : ZM R FL (ch := ch), u ∈ consM R FL Pl lhat n o z := by
  classical
  set L := load R ch FL lhat (nn n) (oo R FL Pl o) with hL
  have one : ∀ x : RM T m AA, okR T R ch x → ActR L x → tgU R FL Pl u = inpR T x →
      ∃ z : ZM R FL (ch := ch), u ∈ consM R FL Pl lhat n o z := by
    intro x hx ha ht
    exact ⟨⟨.inl ⟨x, hx⟩, ()⟩, (consM_inl _ _ u).2 ⟨ha, hu, ht⟩⟩
  rcases hτ : tgU R FL Pl u with _ | ⟨j, e⟩ | x | ⟨j, i, ω, q⟩
  · exact absurd hτ hd
  · revert e
    refine Fin.lastCases ?_ (fun j => ?_) j
    · intro e hτ
      exact one (.fin e) trivial trivial hτ
    · intro e hτ
      obtain ⟨i, hi⟩ := exists_isMin hh L j.castSucc
      by_cases ht : T.ty e = i
      · refine one (.mid j e 0) ⟨fun h3 => absurd h3 (by decide), fun h3 => absurd h3 (by decide)⟩ (fun _ => ?_) ?_
        · rw [ht]; exact hi
        · rw [hτ, inpR_mid, if_pos rfl]
      · exact one (.inn j i e) ht hi hτ
  · have h1 : okR T R ch x ∧ inpR T x = .nxt x ∧ ∀ L : Tg T m AA → ℕ, ActR L x := by
      cases u with
      | init a c k => exact nxt_ok_B hτ
      | new ν k =>
        have hτ : tgM R ch FL (eN R FL Pl ν).1 (eN R FL Pl ν).2 = .nxt x := hτ
        revert hτ
        generalize eN R FL Pl ν = w
        intro hτ
        rcases w with ⟨⟨y, hy⟩ | l, w⟩
        · exact nxt_ok_R hy hτ
        · simp [tgM] at hτ
    exact one x h1.1 (h1.2.2 L) (hτ.trans h1.2.1.symm)
  · -- an end segment
    have hq : ¬ q.IsDiag := by
      cases u with
      | init a c k =>
        exfalso
        have hτ : tgB T R ch a c k = .seg j i ω q := hτ
        rcases tgB_cases (R := R) (ch := ch) a c k with h1 | ⟨hm, h1⟩ | ⟨e', -, h1, -⟩ <;> rw [h1] at hτ <;> cases hτ
      | new ν k => exact seg_nondiag hr hb (ν := eN R FL Pl ν) hτ
    obtain ⟨t0, d0, -⟩ := exists_fits_seg (FL := FL) L j i ω
    obtain ⟨d, hd⟩ := exists_pick L (⟨j, i, ω, d0⟩ : LMv T FL)
    have hd : Pick FL L (⟨j, i, ω, d⟩ : LMv T FL) := hd
    have hnum : num R ch FL lhat (nn n) (oo R FL Pl o) (.inr (⟨j, i, ω, d⟩ : LMv T FL)) = tmin FL L (⟨j, i, ω, d⟩ : LMv T FL) := by
      rw [num_eq hr hb, numF, if_pos hd]
    set t := tmin FL L (⟨j, i, ω, d⟩ : LMv T FL) with ht
    have hfit := hd.1 q hq
    have hrk : rkU R FL Pl lhat n o u < L (.seg j i ω q) := by
      rw [hL, load_eq]
      have := rk_lt (idx := ix R FL Pl) (key := tgU R FL Pl) (mem_Al.2 hu)
      rw [hτ] at this
      exact this
    have hlt : rkU R FL Pl lhat n o u < slo FL d q * t := lt_of_lt_of_le hrk hfit
    have htpos : 0 < t := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · rw [h0, Nat.mul_zero] at hlt
        exact absurd hlt (Nat.not_lt_zero _)
      · exact h0
    have hw : rkU R FL Pl lhat n o u / t < slo FL d q := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hlt)
    obtain ⟨e, -, he1, he2⟩ := exists_rk (idx := fun e => (Fintype.equivFin (FL.L d).Sl e).1) (key := pr FL d)
      (fun a b hab => (Fintype.equivFin (FL.L d).Sl).injective (Fin.ext hab)) univ q hw
    have he2 : su FL d e = rkU R FL Pl lhat n o u / t := he2
    refine ⟨⟨.inr ⟨j, i, ω, d⟩, e⟩, (consM_inr (⟨j, i, ω, d⟩ : LMv T FL) e u).2 ⟨hd, hu, ?_, ?_, ?_⟩⟩
    · rw [hτ, he1]
    · rw [hnum, he2]
      exact Nat.div_mul_le_self _ _
    · rw [hnum, he2, Nat.add_mul, Nat.one_mul, Nat.mul_comm]
      exact Nat.lt_mul_div_succ _ htpos |>.trans_eq (by ring)

/-- The units that are seen. -/
theorem mem_seen_new {ν : (sys R FL Pl).N} {k : Fin U1} :
    (Uid.new ν k : Un R FL Pl U0 U1) ∈ Plan.seenAt (M := sys R FL Pl) n o (Fintype.card (Mv T R ch FL)) ↔ k ≤ o ν := by
  unfold Plan.seenAt
  rw [mem_union, mem_biUnion]
  constructor
  · rintro (h1 | ⟨x, -, h2⟩)
    · simp [seen0] at h1
    · simp only [newUnits, mem_filter, mem_univ, true_and, decide_eq_true_eq] at h2
      exact h2.2
  · intro h1
    right
    refine ⟨ν.1, mem_filter.2 ⟨mem_univ _, ν.1.2⟩, ?_⟩
    simp only [newUnits, mem_filter, mem_univ, true_and, decide_eq_true_eq]
    exact h1

theorem mem_seen_init {a c : Fin AA} {k : Fin U0} :
    (Uid.init a c k : Un R FL Pl U0 U1) ∈ Plan.seenAt (M := sys R FL Pl) n o (Fintype.card (Mv T R ch FL)) ↔ k.1 < (n a c).1 := by
  unfold Plan.seenAt
  rw [mem_union, mem_biUnion]
  constructor
  · rintro (h1 | ⟨x, -, h2⟩)
    · simpa [seen0] using h1
    · simp [newUnits] at h2
  · intro h1
    left
    simpa [seen0] using h1

/-- **The current units in the end**: alive units between a node and its parent, and dead units. -/
theorem cur_end (hr : 0 < r) (hb : 0 < b) (hh : 0 < h) {u : Un R FL Pl U0 U1}
    (hu : u ∈ (plan R FL Pl lhat U0 U1).cur n o (Fintype.card (Mv T R ch FL))) :
    u ∈ Plan.seenAt (M := sys R FL Pl) n o (Fintype.card (Mv T R ch FL)) ∧
      (AlU R FL Pl lhat n o u → tgU R FL Pl u = .done) := by
  rw [Plan.cur, mem_sdiff] at hu
  refine ⟨hu.1, fun ha => ?_⟩
  by_contra hd
  obtain ⟨z, hz⟩ := exists_cons hr hb hh ha hd
  apply hu.2
  unfold Plan.used
  rw [mem_biUnion]
  refine ⟨(eZ R FL Pl).symm z, mem_filter.2 ⟨mem_univ _, ((eZ R FL Pl).symm z).1.2⟩, ?_⟩
  change u ∈ consM R FL Pl lhat n o (eZ R FL Pl ((eZ R FL Pl).symm z))
  rw [Equiv.apply_symm_apply]
  exact hz

end Plan

end Nc.Tow
