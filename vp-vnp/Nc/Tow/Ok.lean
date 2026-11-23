/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Plan

/-!
# The tower plan obeys the rules
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b D J r m Uu AA A' U0 U1 : ℕ} {T : Tower h b D J r} {R : Routes T m Uu}
  {ch : Fin AA ↪ T.X 0} {FL : FlagLaws F T} {Pl : Place T ch A'} {lhat : ℕ}

theorem isMin_unique {L : Tg T m AA → ℕ} {j : Fin (J + 1)} {i i' : Fin h} (h1 : IsMin L j i) (h2 : IsMin L j i') :
    i = i' := by
  rcases lt_trichotomy i i' with hlt | heq | hlt
  · exact absurd h1.1 (h2.2 i hlt)
  · exact heq
  · exact absurd h2.1 (h1.2 i' hlt)

theorem pick_unique {L : Tg T m AA → ℕ} {l : LMv T FL} {d : FL.Di} (h1 : Pick FL L l) (h2 : Pick FL L (withD FL l d)) :
    l.2.2.2 = d := by
  have e : tmin FL L (withD FL l d) = tmin FL L l := rfl
  rcases lt_trichotomy (Fintype.equivFin FL.Di d) (Fintype.equivFin FL.Di l.2.2.2) with hlt | heq | hlt
  · exact absurd h2.1 (h1.2 d hlt)
  · exact ((Fintype.equivFin FL.Di).injective heq).symm
  · exact absurd h1.1 (h2.2 l.2.2.2 hlt)

/-- Active relays are determined by their targets. -/
theorem inpR_unique {L : Tg T m AA → ℕ} {x x' : RM T m AA} (hx : okR T R ch x) (hx' : okR T R ch x')
    (ha : ActR L x) (ha' : ActR L x') (he : inpR T x = inpR T x') : x = x' := by
  rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e <;>
    rcases x' with ⟨a', c', γ', s'⟩ | ⟨j', i', e'⟩ | ⟨j', e', s'⟩ | e'
  · simpa [inpR] using he
  · simp [inpR] at he
  · rw [inpR_mid] at he
    split_ifs at he <;> simp [inpR] at he
  · simp [inpR] at he
  · simp [inpR] at he
  · simp only [inpR, Tg.edge.injEq] at he
    obtain ⟨h1, h2⟩ := he
    have hj : j = j' := Fin.castSucc_injective _ h1
    subst hj
    have := eq_of_heq h2
    subst this
    rw [isMin_unique ha ha']
  · rw [inpR_mid] at he
    split_ifs at he with hs
    · simp only [inpR, Tg.edge.injEq] at he
      obtain ⟨h1, h2⟩ := he
      have hj : j = j' := Fin.castSucc_injective _ h1
      subst hj
      have := eq_of_heq h2
      subst this
      exact absurd (isMin_unique (ha' hs) ha) hx
    · simp [inpR] at he
  · simp only [inpR, Tg.edge.injEq] at he
    exact absurd he.1 (Fin.castSucc_lt_last j).ne
  · rw [inpR_mid] at he
    split_ifs at he <;> simp [inpR] at he
  · rw [inpR_mid] at he
    split_ifs at he with hs
    · simp only [inpR, Tg.edge.injEq] at he
      obtain ⟨h1, h2⟩ := he
      have hj : j = j' := Fin.castSucc_injective _ h1
      subst hj
      have := eq_of_heq h2
      subst this
      exact absurd (isMin_unique (ha hs) ha') hx'
    · simp [inpR] at he
  · rw [inpR_mid, inpR_mid] at he
    split_ifs at he with hs hs' hs'
    · simp only [Tg.edge.injEq] at he
      obtain ⟨h1, h2⟩ := he
      have hj : j = j' := Fin.castSucc_injective _ h1
      subst hj
      have := eq_of_heq h2
      subst this
      rw [hs, hs']
    · simpa using he
  · rw [inpR_mid] at he
    split_ifs at he with hs
    · simp only [inpR, Tg.edge.injEq] at he
      exact absurd he.1 (Fin.castSucc_lt_last j).ne
    · simp [inpR] at he
  · simp [inpR] at he
  · simp only [inpR, Tg.edge.injEq] at he
    exact absurd he.1.symm (Fin.castSucc_lt_last j').ne
  · rw [inpR_mid] at he
    split_ifs at he with hs
    · simp only [inpR, Tg.edge.injEq] at he
      exact absurd he.1.symm (Fin.castSucc_lt_last j').ne
    · simp [inpR] at he
  · simpa [inpR] using he

theorem inpR_ne_seg {x : RM T m AA} {j : Fin J} {i : Fin h} {ω : T.V (j + 1) i} {q : Sym2 T.Fl} :
    inpR T x ≠ .seg j i ω q := by
  rcases x with ⟨a, c, γ, s⟩ | ⟨j', i', e⟩ | ⟨j', e, s⟩ | e
  · simp [inpR]
  · simp [inpR]
  · rw [inpR_mid]
    split_ifs <;> simp
  · simp [inpR]

theorem inpR_ne_done {x : RM T m AA} : inpR T x ≠ .done := by
  rcases x with ⟨a, c, γ, s⟩ | ⟨j', i', e⟩ | ⟨j', e, s⟩ | e
  · simp [inpR]
  · simp [inpR]
  · rw [inpR_mid]
    split_ifs <;> simp
  · simp [inpR]

theorem su_inj {d : FL.Di} {e e' : (FL.L d).Sl} (hp : pr FL d e = pr FL d e') (hs : su FL d e = su FL d e') : e = e' :=
  rk_inj (fun a b hab => (Fintype.equivFin (FL.L d).Sl).injective (Fin.ext hab)) (mem_univ _) (mem_univ _) hp hs

section Plan

variable {n : Fin AA → Fin AA → Fin (U0 + 1)} {o : (sys R FL Pl).N → Fin U1}

/-- The target of the units of a slot. -/
def inpZ : ZM R FL (ch := ch) → Tg T m AA
  | ⟨.inl x, _⟩ => inpR T x.1
  | ⟨.inr l, e⟩ => .seg l.1 l.2.1 l.2.2.1 (pr FL l.2.2.2 e)

theorem consM_inl (x : {x : RM T m AA // okR T R ch x}) (e : (kindM R ch FL (.inl x)).Sl) (u : Un R FL Pl U0 U1) :
    u ∈ consM R FL Pl lhat n o ⟨.inl x, e⟩ ↔ ActR (load R ch FL lhat (nn n) (oo R FL Pl o)) x.1 ∧
      AlU R FL Pl lhat n o u ∧ tgU R FL Pl u = inpR T x.1 := by
  classical
  rw [consM]
  split_ifs with ha
  · simp [mem_Al, ha]
  · simp [ha]

theorem consM_inr (l : LMv T FL) (e : (kindM R ch FL (.inr l)).Sl) (u : Un R FL Pl U0 U1) :
    u ∈ consM R FL Pl lhat n o ⟨.inr l, e⟩ ↔ Pick FL (load R ch FL lhat (nn n) (oo R FL Pl o)) l ∧
      AlU R FL Pl lhat n o u ∧ tgU R FL Pl u = .seg l.1 l.2.1 l.2.2.1 (pr FL l.2.2.2 e) ∧
        su FL l.2.2.2 e * num R ch FL lhat (nn n) (oo R FL Pl o) (.inr l) ≤ rkU R FL Pl lhat n o u ∧
        rkU R FL Pl lhat n o u < (su FL l.2.2.2 e + 1) * num R ch FL lhat (nn n) (oo R FL Pl o) (.inr l) := by
  classical
  rw [consM]
  split_ifs with ha
  · simp [mem_Al, ha]
  · simp [ha]

theorem consM_al {z : ZM R FL (ch := ch)} {u : Un R FL Pl U0 U1} (hu : u ∈ consM R FL Pl lhat n o z) :
    AlU R FL Pl lhat n o u ∧ tgU R FL Pl u = inpZ z := by
  rcases z with ⟨x | l, e⟩
  · exact ((consM_inl x e u).1 hu).2
  · have := ((consM_inr l e u).1 hu).2
    exact ⟨this.1, this.2.1⟩

theorem inpZ_ne_done (z : ZM R FL (ch := ch)) : inpZ z ≠ .done := by
  rcases z with ⟨x | l, e⟩
  · exact inpR_ne_done
  · simp [inpZ]

theorem inpZ_time (z : ZM R FL (ch := ch)) : tgTime (inpZ z) ≤ timeM R ch FL z.1 := by
  rcases z with ⟨x | l, e⟩
  · exact inp_time x.1
  · exact le_rfl

/-- A unit is given at one slot at most. -/
theorem consM_unique {z z' : ZM R FL (ch := ch)} {u : Un R FL Pl U0 U1} (hu : u ∈ consM R FL Pl lhat n o z)
    (hu' : u ∈ consM R FL Pl lhat n o z') : z = z' := by
  rcases z with ⟨x | l, e⟩ <;> rcases z' with ⟨x' | l', e'⟩
  · obtain ⟨h1, -, h2⟩ := (consM_inl x e u).1 hu
    obtain ⟨h1', -, h2'⟩ := (consM_inl x' e' u).1 hu'
    have hx : x = x' := Subtype.ext (inpR_unique x.2 x'.2 h1 h1' (h2.symm.trans h2'))
    subst hx
    rfl
  · obtain ⟨-, -, h2⟩ := (consM_inl x e u).1 hu
    obtain ⟨-, -, h2', -⟩ := (consM_inr l' e' u).1 hu'
    exact absurd (h2.symm.trans h2') inpR_ne_seg
  · obtain ⟨-, -, h2, -⟩ := (consM_inr l e u).1 hu
    obtain ⟨-, -, h2'⟩ := (consM_inl x' e' u).1 hu'
    exact absurd (h2'.symm.trans h2) inpR_ne_seg
  · obtain ⟨h1, -, h2, h3, h4⟩ := (consM_inr l e u).1 hu
    obtain ⟨h1', -, h2', h3', h4'⟩ := (consM_inr l' e' u).1 hu'
    obtain ⟨j, i, ω, d⟩ := l
    obtain ⟨j', i', ω', d'⟩ := l'
    have he := h2.symm.trans h2'
    simp only [Tg.seg.injEq] at he
    obtain ⟨hj, hi, hω, hq⟩ := he
    subst hj
    subst hi
    have := eq_of_heq hω
    subst this
    have hd : d = d' := pick_unique (l := ⟨j, i, ω, d⟩) h1 h1'
    subst hd
    simp only at h3 h4 h3' h4' hq
    have hs : su FL d e = su FL d e' := by
      set t := num R ch FL lhat (nn n) (oo R FL Pl o) (.inr ⟨j, i, ω, d⟩)
      rcases lt_trichotomy (su FL d e) (su FL d e') with hlt | heq | hlt
      · have : (su FL d e + 1) * t ≤ su FL d e' * t := Nat.mul_le_mul_right t hlt
        omega
      · exact heq
      · have : (su FL d e' + 1) * t ≤ su FL d e * t := Nat.mul_le_mul_right t hlt
        omega
    have hee : e = e' := su_inj hq hs
    subst hee
    rfl

/-- The number of units of a slot. -/
theorem card_consM (hr : 0 < r) (hb : 0 < b) (z : ZM R FL (ch := ch)) :
    (consM R FL Pl lhat n o z : Finset (Un R FL Pl U0 U1)).card ≤ num R ch FL lhat (nn n) (oo R FL Pl o) z.1 := by
  classical
  rcases z with ⟨x | l, e⟩
  · rw [num_eq hr hb, consM, numF]
    split_ifs with ha
    · rw [load_eq]
    · simp
  · rw [consM]
    split_ifs with ha
    · refine (card_rk_le (ix_inj (R := R) (FL := FL) (Pl := Pl)) (Al R FL Pl lhat n o)
        (Tg.seg l.1 l.2.1 l.2.2.1 (pr FL l.2.2.2 e) : Tg T m AA) _ _).trans ?_
      rw [Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel_left]
    · simp

theorem time_lt_of_tg {ν : NM R FL (ch := ch)} {z : ZM R FL (ch := ch)} (hν : tgM R ch FL ν.1 ν.2 = inpZ z) :
    timeM R ch FL ν.1 < timeM R ch FL z.1 := by
  have h1 := tg_time ν
  rw [hν] at h1
  exact lt_of_lt_of_le h1 (inpZ_time z)

theorem lt_of_time {x y : Fin (Fintype.card (Mv T R ch FL))}
    (hxy : timeM R ch FL (eE R FL x) < timeM R ch FL (eE R FL y)) : x < y := by
  have := eE_lt R FL hxy
  rwa [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at this

/-- The holders of a unit. -/
theorem holds_eq {u : Un R FL Pl U0 U1} (hd : tgU R FL Pl u ≠ .done) :
    s(hold0 (sys R FL Pl).np u, hold1 (sys R FL Pl).np u) = (hT R ch (tgU R FL Pl u)).map Pl.pt := by
  cases u with
  | init a c k =>
    have h1 := hB_eq (ch := ch) (R := R) hd
    change _ = (hT R ch (tgB T R ch a c k)).map Pl.pt
    rw [← h1, hB, Sym2.map_mk]
    simp only [Prod.map, Pl.pt_base]
    rfl
  | new ν k =>
    have h1 := hN_eq (eN R FL Pl ν) hd
    change _ = (hT R ch (tgM R ch FL (eN R FL Pl ν).1 (eN R FL Pl ν).2)).map Pl.pt
    rw [← h1, hN, Sym2.map_mk]
    rfl

/-- The ends of a slot. -/
theorem zp_hold (z : (sys R FL Pl).Z) :
    s((sys R FL Pl).zp z false, (sys R FL Pl).zp z true) = (hT R ch (inpZ (eZ R FL Pl z))).map Pl.pt := by
  rw [zp_eq, zp_eq]
  generalize eZ R FL Pl z = w
  rcases w with ⟨⟨x, hx⟩ | l, e⟩
  · change s(Pl.pt (tri T R ch x 0), Pl.pt (tri T R ch x 2)) = (hT R ch (inpR T x)).map Pl.pt
    have h1 : hT R ch (inpR T x) = s(tri T R ch x 0, tri T R ch x 2) := by
      rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e
      · rfl
      · rfl
      · rw [inpR_mid]
        split_ifs with hs
        · subst hs; rfl
        · rfl
      · rfl
    rw [h1, Sym2.map_mk]
  · change s(Pl.pt (nd T (l.1 + 1) l.1.2 (atv l.1.2 l.2.1 l.2.2.1 (FL.ro l.2.2.2 ((FL.L l.2.2.2).a e)))),
      Pl.pt (nd T (l.1 + 1) l.1.2 (atv l.1.2 l.2.1 l.2.2.1 (FL.ro l.2.2.2 ((FL.L l.2.2.2).b e))))) = _
    simp only [inpZ, hT, pr, Sym2.map_mk, Prod.map]

section Causal

variable {o' : (sys R FL Pl).N → Fin U1} {t : ℕ}

theorem alU_congr (hr : 0 < r) (hb : 0 < b) (hag : ∀ mv' : Mv T R ch FL, timeM R ch FL mv' < t →
    ∀ c, oo R FL Pl o ⟨mv', c⟩ = oo R FL Pl o' ⟨mv', c⟩) {u : Un R FL Pl U0 U1} (hu : tgTime (tgU R FL Pl u) ≤ t) :
    AlU R FL Pl lhat n o u ↔ AlU R FL Pl lhat n o' u := by
  cases u with
  | init a c k => exact Iff.rfl
  | new ν k =>
    have h1 : timeM R ch FL (eN R FL Pl ν).1 < t := lt_of_lt_of_le (tg_time (eN R FL Pl ν)) hu
    have h2 : alv R ch FL lhat (nn n) (oo R FL Pl o) (eN R FL Pl ν) =
        alv R ch FL lhat (nn n) (oo R FL Pl o') (eN R FL Pl ν) := by
      unfold alv
      rw [num_congr hr hb fun mv' hmv' c => hag mv' (hmv'.trans h1) c]
      exact alvN_congr (fun c => hag _ h1 c) _
    change k.1 < alv R ch FL lhat (nn n) (oo R FL Pl o) (eN R FL Pl ν) ↔
      k.1 < alv R ch FL lhat (nn n) (oo R FL Pl o') (eN R FL Pl ν)
    rw [h2]

theorem consM_congr_inl (hr : 0 < r) (hb : 0 < b) (x : {x : RM T m AA // okR T R ch x}) (e : (kindM R ch FL (.inl x)).Sl)
    (hag : ∀ mv' : Mv T R ch FL, timeM R ch FL mv' < timeM R ch FL (.inl x) →
      ∀ c, oo R FL Pl o ⟨mv', c⟩ = oo R FL Pl o' ⟨mv', c⟩) (u : Un R FL Pl U0 U1) :
    u ∈ consM R FL Pl lhat n o ⟨.inl x, e⟩ ↔ u ∈ consM R FL Pl lhat n o' ⟨.inl x, e⟩ := by
  rw [consM_inl, consM_inl]
  have h1 : ActR (load R ch FL lhat (nn n) (oo R FL Pl o)) x.1 ↔ ActR (load R ch FL lhat (nn n) (oo R FL Pl o')) x.1 :=
    actR_congr fun τ hτ => load_congr hr hb hτ hag
  rw [h1]
  refine and_congr_right fun _ => ?_
  have h2 : tgU R FL Pl u = inpR T x.1 → (AlU R FL Pl lhat n o u ↔ AlU R FL Pl lhat n o' u) := by
    intro hu
    refine alU_congr hr hb hag ?_
    rw [hu]
    exact inp_time x.1
  constructor
  · rintro ⟨h3, h4⟩
    exact ⟨(h2 h4).1 h3, h4⟩
  · rintro ⟨h3, h4⟩
    exact ⟨(h2 h4).2 h3, h4⟩

theorem consM_congr_inr (hr : 0 < r) (hb : 0 < b) (l : LMv T FL) (e : (kindM R ch FL (.inr l)).Sl)
    (hag : ∀ mv' : Mv T R ch FL, timeM R ch FL mv' < timeM R ch FL (.inr l) →
      ∀ c, oo R FL Pl o ⟨mv', c⟩ = oo R FL Pl o' ⟨mv', c⟩) (u : Un R FL Pl U0 U1) :
    u ∈ consM R FL Pl lhat n o ⟨.inr l, e⟩ ↔ u ∈ consM R FL Pl lhat n o' ⟨.inr l, e⟩ := by
  have hpk : Pick FL (load R ch FL lhat (nn n) (oo R FL Pl o)) l ↔ Pick FL (load R ch FL lhat (nn n) (oo R FL Pl o')) l :=
    pick_congr fun q => load_congr hr hb (le_refl _) hag
  have hnum : num R ch FL lhat (nn n) (oo R FL Pl o) (.inr l) = num R ch FL lhat (nn n) (oo R FL Pl o') (.inr l) :=
    num_congr hr hb hag
  have hal : ∀ v : Un R FL Pl U0 U1, tgU R FL Pl v = .seg l.1 l.2.1 l.2.2.1 (pr FL l.2.2.2 e) →
      (AlU R FL Pl lhat n o v ↔ AlU R FL Pl lhat n o' v) := by
    intro v hv
    refine alU_congr hr hb hag ?_
    rw [hv]
    exact le_refl _
  have hrk : tgU R FL Pl u = .seg l.1 l.2.1 l.2.2.1 (pr FL l.2.2.2 e) →
      rkU R FL Pl lhat n o u = rkU R FL Pl lhat n o' u := by
    intro hu
    unfold rkU
    exact rk_congr fun v hv => mem_Al.trans ((hal v (hv.trans hu)).trans mem_Al.symm)
  rw [consM_inr, consM_inr, hpk, hnum]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [hrk h2] at h3
    exact ⟨(hal u h2).1 h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    rw [← hrk h2] at h3
    exact ⟨(hal u h2).2 h1, h2, h3⟩

theorem consM_congr (hr : 0 < r) (hb : 0 < b) (z : ZM R FL (ch := ch))
    (hag : ∀ mv' : Mv T R ch FL, timeM R ch FL mv' < timeM R ch FL z.1 →
      ∀ c, oo R FL Pl o ⟨mv', c⟩ = oo R FL Pl o' ⟨mv', c⟩) :
    (consM R FL Pl lhat n o z : Finset (Un R FL Pl U0 U1)) = consM R FL Pl lhat n o' z := by
  ext u
  rcases z with ⟨x | l, e⟩
  · exact consM_congr_inl hr hb x e hag u
  · exact consM_congr_inr hr hb l e hag u

theorem agree_of (ho : ∀ ν : (sys R FL Pl).N, timeM R ch FL (eE R FL ν.1) < t → o ν = o' ν) :
    ∀ mv' : Mv T R ch FL, timeM R ch FL mv' < t → ∀ c, oo R FL Pl o ⟨mv', c⟩ = oo R FL Pl o' ⟨mv', c⟩ := by
  intro mv' hmv' c
  unfold oo
  rw [ho]
  have h1 : (eN R FL Pl ((eN R FL Pl).symm ⟨mv', c⟩)).1 = mv' := by rw [Equiv.apply_symm_apply]
  rw [eN_fst] at h1
  rw [h1]
  exact hmv'

end Causal

/-- Units that are given are current. -/
theorem consM_cur {z : (sys R FL Pl).Z} {u : Un R FL Pl U0 U1} (hu : u ∈ consM R FL Pl lhat n o (eZ R FL Pl z)) :
    u ∈ (plan R FL Pl lhat U0 U1).cur n o z.1 := by
  obtain ⟨h1, h2⟩ := consM_al hu
  rw [Plan.cur, mem_sdiff]
  constructor
  · unfold Plan.seenAt
    rw [mem_union, mem_biUnion]
    cases u with
    | init a c k =>
      left
      simp only [seen0, mem_filter, mem_univ, true_and, decide_eq_true_eq]
      exact h1.2
    | new ν k =>
      right
      refine ⟨ν.1, mem_filter.2 ⟨mem_univ _, ?_⟩, ?_⟩
      · have h3 := time_lt_of_tg (ν := eN R FL Pl ν) (z := eZ R FL Pl z) h2
        rw [eN_fst, eZ_fst] at h3
        exact lt_of_time h3
      · simp only [newUnits, mem_filter, mem_univ, true_and, decide_eq_true_eq]
        have h3 : k.1 < alv R ch FL lhat (nn n) (oo R FL Pl o) (eN R FL Pl ν) := h1
        have h4 : alv R ch FL lhat (nn n) (oo R FL Pl o) (eN R FL Pl ν) ≤ (o ν).1 := by
          refine (alvN_le _ _).trans ?_
          unfold oo
          rw [Equiv.symm_apply_apply]
        rw [Fin.le_def]
        omega
  · intro hmem
    unfold Plan.used at hmem
    rw [mem_biUnion] at hmem
    obtain ⟨z', hz', hu'⟩ := hmem
    have hlt := (mem_filter.1 hz').2
    have hu' : u ∈ consM R FL Pl lhat n o (eZ R FL Pl z') := hu'
    have hzz := (eZ R FL Pl).injective (consM_unique hu hu')
    rw [hzz] at hlt
    exact lt_irrefl _ hlt

/-- **The plan obeys the rules.** -/
theorem plan_ok (hr : 0 < r) (hb : 0 < b) {cap : ℕ}
    (hcap : ∀ (n : Fin AA → Fin AA → Fin (U0 + 1)) (o : (sys R FL Pl).N → Fin U1) mv,
      num R ch FL lhat (nn n) (oo R FL Pl o) mv ≤ cap) : (plan R FL Pl lhat U0 U1).Ok cap where
  causal n o o' z ho := by
    refine consM_congr hr hb (eZ R FL Pl z) (agree_of fun ν hν => ho ν ?_)
    rw [eZ_fst] at hν
    exact lt_of_time hν
  causal' n o o' x ho := by
    refine num_congr hr hb (agree_of fun ν hν => ho ν ?_)
    exact lt_of_time hν
  causal'' n o o' x ho := by
    refine good_congr hr hb (agree_of fun ν hν => ho ν (lt_of_time hν).le) fun c => ?_
    unfold oo
    rw [ho]
    have h1 : (eN R FL Pl ((eN R FL Pl).symm ⟨eE R FL x, c⟩)).1 = eE R FL x := by rw [Equiv.apply_symm_apply]
    rw [eN_fst] at h1
    exact ((eE R FL).injective h1).le
  sub n o z u hu := consM_cur hu
  hold n o z u hu := by
    have hu : u ∈ consM R FL Pl lhat n o (eZ R FL Pl z) := hu
    obtain ⟨-, h2⟩ := consM_al hu
    have h3 := holds_eq (u := u) (by rw [h2]; exact inpZ_ne_done _)
    rw [h2, ← zp_hold, Sym2.eq_iff] at h3
    rcases h3 with h3 | h3
    · exact Or.inl h3
    · exact Or.inr ⟨h3.2, h3.1⟩
  disj n o x e e' hee := by
    rw [disjoint_left]
    intro u hu hu'
    have hu : u ∈ consM R FL Pl lhat n o (eZ R FL Pl ⟨x, e⟩) := hu
    have hu' : u ∈ consM R FL Pl lhat n o (eZ R FL Pl ⟨x, e'⟩) := hu'
    have h1 := (eZ R FL Pl).injective (consM_unique hu hu')
    rw [Sigma.mk.injEq] at h1
    exact hee (eq_of_heq h1.2)
  card n o z := card_consM hr hb (eZ R FL Pl z)
  cap n o x := hcap n o _

end Plan

end Nc.Tow
