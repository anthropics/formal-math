/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Tow.Relay
import Nc.Tow.Path

/-!
# The tower plan: nodes, moves, targets

Every channel has a target: what becomes of its units. `done`: they stay between a node and its parent; `edge j e`:
units of stage `j` on the edge `e`; `nxt x`: given in the relay `x`; `seg …`: end segments on a pair of a vertex.
-/

set_option linter.unusedSectionVars false

namespace Nc.Tow

open Finset Nc.G

variable {F : Type} [CommRing F] {h b D J r m Uu AA : ℕ}

/-- Nodes of the tree: the chambers of all levels, and the root. -/
abbrev Nd (T : Tower h b D J r) := Option (Σ j : Fin (J + 1), T.X j)

/-- The node of a chamber. -/
def nd (T : Tower h b D J r) (j : ℕ) (hj : j ≤ J) (c : T.X j) : Nd T := some ⟨⟨j, Nat.lt_succ_of_le hj⟩, c⟩

theorem nd_inj {T : Tower h b D J r} {j : ℕ} {hj hj' : j ≤ J} {c c' : T.X j} :
    nd T j hj c = nd T j hj' c' ↔ c = c' := by
  unfold nd
  rw [Option.some_inj, Sigma.mk.injEq]
  simp

theorem nd_ne {T : Tower h b D J r} {j j' : ℕ} (hjj : j ≠ j') {hj : j ≤ J} {hj' : j' ≤ J} {c : T.X j} {c' : T.X j'} :
    nd T j hj c ≠ nd T j' hj' c' := by
  unfold nd
  rw [Ne, Option.some_inj, Sigma.mk.injEq]
  rintro ⟨h1, -⟩
  exact hjj (congrArg Fin.val h1)

theorem nd_ne_none {T : Tower h b D J r} {j : ℕ} {hj : j ≤ J} {c : T.X j} : nd T j hj c ≠ none := by
  unfold nd; exact Option.some_ne_none _

/-- Names of relays. -/
inductive RM (T : Tower h b D J r) (m AA : ℕ) where
  /-- step `s` of the path of a batch -/
  | start (a c : Fin AA) (γ : T.X 0) (s : Fin (2 * m))
  /-- an edge inside a vertex of type `i` -/
  | inn (j : Fin J) (i : Fin h) (e : T.Ed j)
  /-- an edge between vertices of its type -/
  | mid (j : Fin J) (e : T.Ed j) (s : Fin 4)
  /-- the last stage -/
  | fin (e : T.Ed J)

/-- Relays as a sum. -/
def rmEquiv (T : Tower h b D J r) (m AA : ℕ) : RM T m AA ≃ (Fin AA × Fin AA × T.X 0 × Fin (2 * m)) ⊕
    ((Σ j : Fin J, Fin h × T.Ed j) ⊕ ((Σ j : Fin J, T.Ed j × Fin 4) ⊕ T.Ed J)) where
  toFun
    | .start a c γ s => .inl (a, c, γ, s)
    | .inn j i e => .inr (.inl ⟨j, i, e⟩)
    | .mid j e s => .inr (.inr (.inl ⟨j, e, s⟩))
    | .fin e => .inr (.inr (.inr e))
  invFun
    | .inl x => .start x.1 x.2.1 x.2.2.1 x.2.2.2
    | .inr (.inl x) => .inn x.1 x.2.1 x.2.2
    | .inr (.inr (.inl x)) => .mid x.1 x.2.1 x.2.2
    | .inr (.inr (.inr e)) => .fin e
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with _ | _ | _ | _ <;> rfl

instance (T : Tower h b D J r) (m AA : ℕ) : Fintype (RM T m AA) := Fintype.ofEquiv _ (rmEquiv T m AA).symm

/-- Targets. -/
inductive Tg (T : Tower h b D J r) (m AA : ℕ) where
  /-- a node and its parent -/
  | done
  /-- an edge of stage `j` -/
  | edge (j : Fin (J + 1)) (e : T.Ed j)
  /-- given in a relay -/
  | nxt (x : RM T m AA)
  /-- an end segment -/
  | seg (j : Fin J) (i : Fin h) (ω : T.V (j + 1) i) (q : Sym2 T.Fl)

noncomputable instance (T : Tower h b D J r) (m AA : ℕ) : DecidableEq (Tg T m AA) := Classical.decEq _

section

variable (T : Tower h b D J r) (R : Routes T m Uu) (ch : Fin AA ↪ T.X 0)

/-- The host of an end of an edge. -/
abbrev hst {j : ℕ} (i : Fin h) (c : T.X j) : T.X (j + 1) := T.host i (T.vx i c)

/-- The three parties of a relay. -/
def tri : RM T m AA → Fin 3 → Nd T
  | .start a c γ s => ![nd T 0 (Nat.zero_le _) (R.pn (ch a) (ch c) γ s), nd T 0 (Nat.zero_le _) (R.pn (ch a) (ch c) γ (s + 1)),
      nd T 0 (Nat.zero_le _) (ch c)]
  | .inn j i e => ![nd T j j.2.le (T.e0 e), nd T (j + 1) j.2 (hst T i (T.e0 e)), nd T j j.2.le (T.e1 e)]
  | .mid j e s =>
    let H := nd T (j + 1) j.2 (hst T (T.ty e) (T.e0 e))
    let H' := nd T (j + 1) j.2 (hst T (T.ty e) (T.e1 e))
    let p := nd T (j + 1) j.2 (T.π (T.e0 e))
    let p' := nd T (j + 1) j.2 (T.π (T.e1 e))
    ![![nd T j j.2.le (T.e0 e), H, p, p'] s, ![H, p, p', H'] s, nd T j j.2.le (T.e1 e)]
  | .fin e => ![nd T J le_rfl (T.e0 e), none, nd T J le_rfl (T.e1 e)]

/-- The relay exists. -/
def okR : RM T m AA → Prop
  | .start a c γ s => a ≠ c ∧ s.1 + 1 < R.pl (ch a) (ch c) γ
  | .inn _ i e => T.ty e ≠ i
  | .mid _ e s => (s = 1 → hst T (T.ty e) (T.e0 e) ≠ T.π (T.e0 e)) ∧ (s = 3 → T.π (T.e1 e) ≠ hst T (T.ty e) (T.e1 e))
  | .fin _ => True

theorem inj3 {α : Type*} {x y z : α} (h1 : x ≠ y) (h2 : x ≠ z) (h3 : y ≠ z) : Function.Injective ![x, y, z] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

variable {T R ch}

theorem π_ne {j : ℕ} (hj : j < J) (e : T.Ed j) : T.π (T.e0 e) ≠ T.π (T.e1 e) := by
  intro heq
  have h1 := T.π_ends hj e
  rw [heq, Sym2.eq_iff] at h1
  have := T.e_ne (T.πE e)
  rcases h1 with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> exact this (h2.trans h3.symm)

theorem tri_inj {x : RM T m AA} (hx : okR T R ch x) : Function.Injective (tri T R ch x) := by
  rcases x with ⟨a, c, γ, s⟩ | ⟨j, i, e⟩ | ⟨j, e, s⟩ | e
  · obtain ⟨-, h2⟩ := hx
    refine inj3 ?_ ?_ ?_
    · rw [Ne, nd_inj]
      obtain ⟨e, -, -, h3⟩ := R.exists_edge (ch a) (ch c) γ (s := s) (by omega)
      exact h3
    · rw [Ne, nd_inj]
      exact R.pn_ne _ _ _ (by omega)
    · rw [Ne, nd_inj]
      exact R.pn_ne _ _ _ h2
  · exact inj3 (nd_ne (by omega)) (by rw [Ne, nd_inj]; exact T.e_ne e) (nd_ne (by omega))
  · refine inj3 ?_ ?_ ?_
    · fin_cases s
      · change nd T j j.2.le (T.e0 e) ≠ nd T (j + 1) j.2 (hst T (T.ty e) (T.e0 e))
        exact nd_ne (by omega)
      · change nd T (j + 1) j.2 (hst T (T.ty e) (T.e0 e)) ≠ nd T (j + 1) j.2 (T.π (T.e0 e))
        rw [Ne, nd_inj]
        exact hx.1 rfl
      · change nd T (j + 1) j.2 (T.π (T.e0 e)) ≠ nd T (j + 1) j.2 (T.π (T.e1 e))
        rw [Ne, nd_inj]
        exact π_ne j.2 e
      · change nd T (j + 1) j.2 (T.π (T.e1 e)) ≠ nd T (j + 1) j.2 (hst T (T.ty e) (T.e1 e))
        rw [Ne, nd_inj]
        exact hx.2 rfl
    · fin_cases s
      · change nd T j j.2.le (T.e0 e) ≠ nd T j j.2.le (T.e1 e)
        rw [Ne, nd_inj]
        exact T.e_ne e
      · change nd T (j + 1) j.2 (hst T (T.ty e) (T.e0 e)) ≠ nd T j j.2.le (T.e1 e)
        exact nd_ne (by omega)
      · change nd T (j + 1) j.2 (T.π (T.e0 e)) ≠ nd T j j.2.le (T.e1 e)
        exact nd_ne (by omega)
      · change nd T (j + 1) j.2 (T.π (T.e1 e)) ≠ nd T j j.2.le (T.e1 e)
        exact nd_ne (by omega)
    · fin_cases s
      · change nd T (j + 1) j.2 (hst T (T.ty e) (T.e0 e)) ≠ nd T j j.2.le (T.e1 e)
        exact nd_ne (by omega)
      · change nd T (j + 1) j.2 (T.π (T.e0 e)) ≠ nd T j j.2.le (T.e1 e)
        exact nd_ne (by omega)
      · change nd T (j + 1) j.2 (T.π (T.e1 e)) ≠ nd T j j.2.le (T.e1 e)
        exact nd_ne (by omega)
      · change nd T (j + 1) j.2 (hst T (T.ty e) (T.e1 e)) ≠ nd T j j.2.le (T.e1 e)
        exact nd_ne (by omega)
  · exact inj3 nd_ne_none (by rw [Ne, nd_inj]; exact T.e_ne e) nd_ne_none.symm

variable (T R ch)

/-- An edge of stage 0, if there is one. -/
def edgeO : Option (T.Ed 0) → Tg T m AA
  | some e => .edge 0 e
  | none => .done

open Classical in
/-- Targets of the channels of relays. -/
noncomputable def tgR : RM T m AA → Bool → Tg T m AA
  | .start a c γ s, false => edgeO T ((R.path (ch a) (ch c) γ)[s.1]?)
  | .start a c γ s, true =>
    if hs : s.1 + 1 < 2 * m ∧ s.1 + 2 < R.pl (ch a) (ch c) γ then .nxt (.start a c γ ⟨s.1 + 1, hs.1⟩)
    else edgeO T ((R.path (ch a) (ch c) γ)[s.1 + 1]?)
  | .inn _ _ _, _ => .done
  | .mid j e s, false =>
    ![.done, .seg j (T.ty e) (T.πV (T.vx (T.ty e) (T.e0 e))) s(T.co (T.ty e) (hst T (T.ty e) (T.e0 e)), T.co (T.ty e) (T.e0 e)),
      .edge j.succ (T.πE e),
      .seg j (T.ty e) (T.πV (T.vx (T.ty e) (T.e1 e))) s(T.co (T.ty e) (hst T (T.ty e) (T.e1 e)), T.co (T.ty e) (T.e1 e))] s
  | .mid j e s, true =>
    ![if hst T (T.ty e) (T.e0 e) ≠ T.π (T.e0 e) then .nxt (.mid j e 1) else .nxt (.mid j e 2),
      .nxt (.mid j e 2), if T.π (T.e1 e) ≠ hst T (T.ty e) (T.e1 e) then .nxt (.mid j e 3) else .done, .done] s
  | .fin _, _ => .done

/-- The target whose units are given in a relay. -/
def inpR : RM T m AA → Tg T m AA
  | .inn j _ e => .edge j.castSucc e
  | .mid j e s => if s = 0 then .edge j.castSucc e else .nxt (.mid j e s)
  | .fin e => .edge (Fin.last J) e
  | x => .nxt x

/-- Times of relays. -/
def timeR : RM T m AA → ℕ
  | .start _ _ _ s => s
  | .inn j _ _ => 2 * m + 6 * j
  | .mid j _ s => 2 * m + 6 * j + s
  | .fin _ => 2 * m + 6 * J

/-- The third chamber of an initial unit. -/
noncomputable def gam (a : Fin AA) (k : ℕ) : T.X 0 :=
  (Fintype.equivFin (T.X 0)).symm ⟨k % Fintype.card (T.X 0), Nat.mod_lt _ (Fintype.card_pos_iff.2 ⟨ch a⟩)⟩

open Classical in
/-- The target of an initial unit. -/
noncomputable def tgB (a c : Fin AA) (k : ℕ) : Tg T m AA :=
  if a = c then .done
  else if hs : 0 < 2 * m ∧ 1 < R.pl (ch a) (ch c) (gam T ch a k) then .nxt (.start a c (gam T ch a k) ⟨0, hs.1⟩)
  else edgeO T ((R.path (ch a) (ch c) (gam T ch a k))[0]?)

/-- Names of law moves. -/
abbrev LMv (FL : FlagLaws F T) := Σ j : Fin J, Σ i : Fin h, T.V (j + 1) i × FL.Di

/-- Moves. -/
abbrev Mv (FL : FlagLaws F T) := {x : RM T m AA // okR T R ch x} ⊕ LMv T FL

noncomputable instance (FL : FlagLaws F T) : Fintype (Mv T R ch FL) := by
  classical exact inferInstance

variable {T}

/-- The law of a move. -/
def kindM (FL : FlagLaws F T) : Mv T R ch FL → Law F
  | .inl _ => relay F
  | .inr l => FL.L l.2.2.2

/-- A chamber of a vertex. -/
noncomputable def atv {j : ℕ} (hj : j ≤ J) (i : Fin h) (ω : T.V j i) (f : T.Fl) : T.X j :=
  (Equiv.ofBijective _ (T.vx_co hj i)).symm (ω, f)

theorem atv_vx {j : ℕ} (hj : j ≤ J) (i : Fin h) (ω : T.V j i) (f : T.Fl) : T.vx i (atv hj i ω f) = ω := by
  have := (Equiv.ofBijective _ (T.vx_co hj i)).apply_symm_apply (ω, f)
  exact congrArg Prod.fst this

theorem atv_co {j : ℕ} (hj : j ≤ J) (i : Fin h) (ω : T.V j i) (f : T.Fl) : T.co i (atv hj i ω f) = f := by
  have := (Equiv.ofBijective _ (T.vx_co hj i)).apply_symm_apply (ω, f)
  exact congrArg Prod.snd this

theorem atv_eq {j : ℕ} (hj : j ≤ J) (i : Fin h) (c : T.X j) : atv hj i (T.vx i c) (T.co i c) = c :=
  (Equiv.ofBijective _ (T.vx_co hj i)).symm_apply_apply c

/-- The parties of a move. -/
noncomputable def partM (FL : FlagLaws F T) : (mv : Mv T R ch FL) → (kindM R ch FL mv).Ro → Nd T
  | .inl x => fun p => tri T R ch x.1 p
  | .inr l => fun p => nd T (l.1 + 1) l.1.2 (atv l.1.2 l.2.1 l.2.2.1 (FL.ro l.2.2.2 p))

theorem partM_inj (FL : FlagLaws F T) (mv : Mv T R ch FL) : Function.Injective (partM R ch FL mv) := by
  rcases mv with x | l
  · exact tri_inj x.2
  · intro p q hpq
    have h1 : atv l.1.2 l.2.1 l.2.2.1 (FL.ro l.2.2.2 p) = atv l.1.2 l.2.1 l.2.2.1 (FL.ro l.2.2.2 q) :=
      (nd_inj (hj := l.1.2) (hj' := l.1.2)).1 hpq
    have h2 := congrArg (T.co l.2.1) h1
    rw [atv_co, atv_co] at h2
    exact (FL.ro l.2.2.2).injective h2

/-- Times of moves. -/
def timeM (FL : FlagLaws F T) : Mv T R ch FL → ℕ
  | .inl x => timeR T x.1
  | .inr l => 2 * m + 6 * l.1 + 4

/-- Targets of channels. -/
noncomputable def tgM (FL : FlagLaws F T) : (mv : Mv T R ch FL) → (kindM R ch FL mv).Cn → Tg T m AA
  | .inl x => fun ν => tgR T R ch x.1 ν
  | .inr l => fun ν => .edge l.1.succ ((T.nr l.1.2 l.2.1).symm (l.2.2.1, FL.cn l.2.2.2 ν)).1

end

/-- Where the nodes are among the parties. -/
structure Place (T : Tower h b D J r) (ch : Fin AA ↪ T.X 0) (A' : ℕ) where
  /-- the party of a node -/
  pt : Nd T ≃ Fin (AA + A')
  pt_base : ∀ a, pt (nd T 0 (Nat.zero_le _) (ch a)) = Fin.castAdd A' a

section Sys

variable {T : Tower h b D J r} (R : Routes T m Uu) {ch : Fin AA ↪ T.X 0} (FL : FlagLaws F T) {A' : ℕ}
  (Pl : Place T ch A')

/-- The order of the moves. -/
noncomputable def eE : Fin (Fintype.card (Mv T R ch FL)) ≃ Mv T R ch FL :=
  (exists_mono_equiv (timeM R ch FL)).choose

theorem eE_lt {x y : Mv T R ch FL} (hxy : timeM R ch FL x < timeM R ch FL y) :
    (eE R FL).symm x < (eE R FL).symm y := (exists_mono_equiv (timeM R ch FL)).choose_spec x y hxy

/-- The system of moves. -/
noncomputable def sys : Sys F (AA + A') (Fintype.card (Mv T R ch FL)) where
  kind x := kindM R ch FL (eE R FL x)
  part x p := Pl.pt (partM R ch FL (eE R FL x) p)
  inj x := Pl.pt.injective.comp (partM_inj R ch FL _)

/-- Channels by their moves. -/
abbrev NM := Σ mv : Mv T R ch FL, (kindM R ch FL mv).Cn

/-- Slots by their moves. -/
abbrev ZM := Σ mv : Mv T R ch FL, (kindM R ch FL mv).Sl

/-- Channels by their moves. -/
noncomputable def eN : (sys R FL Pl).N ≃ NM R FL (ch := ch) :=
  Equiv.sigmaCongrLeft (β := fun mv => (kindM R ch FL mv).Cn) (eE R FL)

/-- Slots by their moves. -/
noncomputable def eZ : (sys R FL Pl).Z ≃ ZM R FL (ch := ch) :=
  Equiv.sigmaCongrLeft (β := fun mv => (kindM R ch FL mv).Sl) (eE R FL)

theorem eN_fst (ν : (sys R FL Pl).N) : (eN R FL Pl ν).1 = eE R FL ν.1 := rfl

theorem eZ_fst (z : (sys R FL Pl).Z) : (eZ R FL Pl z).1 = eE R FL z.1 := rfl

theorem np_eq (ν : (sys R FL Pl).N) (d : Bool) : (sys R FL Pl).np ν d =
    Pl.pt (partM R ch FL (eN R FL Pl ν).1 ((kindM R ch FL (eN R FL Pl ν).1).cnEnd (eN R FL Pl ν).2 d)) := rfl

theorem zp_eq (z : (sys R FL Pl).Z) (d : Bool) : (sys R FL Pl).zp z d =
    Pl.pt (partM R ch FL (eZ R FL Pl z).1 ((kindM R ch FL (eZ R FL Pl z).1).slEnd (eZ R FL Pl z).2 d)) := rfl

end Sys

end Nc.Tow
