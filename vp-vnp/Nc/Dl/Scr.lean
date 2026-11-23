/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Dl.Run2

/-!
# The templates of the scripts
-/

set_option linter.unusedSectionVars false

namespace Nc.Dl

open NS1 NS1.Tree Finset Nc.G Nc.Cut Codes

section Lists

/-- A list of templates. -/
def listTm : List Tm → Tm
  | [] => .c .nil
  | t :: ts => .cons t (listTm ts)

theorem expand_listTm (σ : List Bool → Tree) (ts : List Tm) : (listTm ts).expand σ = listT (ts.map (Tm.expand σ)) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [listTm, Tm.expand, ih, listT]

/-- A concatenation of templates of lists. -/
def catTm : List Tm → Tm
  | [] => .c .nil
  | t :: ts => .app t (catTm ts)

theorem expand_catTm (σ : List Bool → Tree) (ts : List Tm) :
    (catTm ts).expand σ = listT (ts.flatMap fun t => (t.expand σ).toList) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => rw [catTm, Tm.expand, ih, toList_listT, List.flatMap_cons]

/-- A list if a condition holds, else the empty list. -/
def ifTm (p : List Bool) (t : Tree) (a : Tm) : Tm := .ifeq p t a (.c .nil)

theorem expand_ifTm (σ : List Bool → Tree) (p : List Bool) (t : Tree) (a : Tm) :
    ((ifTm p t a).expand σ).toList = if σ p = t then (a.expand σ).toList else [] := by
  rw [ifTm, Tm.expand]
  split_ifs <;> rfl

theorem flatMap_if {α β : Type*} (l : List α) (p : α → Prop) [DecidablePred p] (f : α → List β) :
    (l.flatMap fun a => if p a then f a else []) = (l.filter p).flatMap f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p a <;> simp [h, ih]

end Lists

variable {A : Type} [CommRing A] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q]
  [DecidableEq Q] {K A' E U0 U1 ub mm D pS c : ℕ} {M : Sys A (K + K + A') E} {P : G.Plan M U0 U1}
  {grp : NN K U0 → (M.N → Fin U1) → Fin (K + K + A') → Fin mm} (C : Codes S M U0 U1 D pS)

section Templates

variable (tab : SlpTab P grp D pS) (tg : M.R → ℕ) (bT bub : List Bool) (gt : Fin mm → Tree) (d1 : Tree)

/-- The value at a name. -/
def gN (x : NmT S M U0 U1 pS) : Tm := .get (C.nm x)

/-- Body of a base party. -/
noncomputable def bodyTm (p : Fin (K + K)) : Tm :=
  .cons (listTm ((univ : Finset (Option S)).toList.map fun s => gN C (.flag s p)))
    (.cons (listTm (List.ofFn fun b => gN C (.kR p b))) (listTm (List.ofFn fun b => gN C (.kC b p))))

/-- Instruction of a base party. -/
noncomputable def baseTm (p : Fin (K + K)) : Tm :=
  Fin.addCases (motive := fun _ => Tm)
    (fun κ => .cons (.c (num 0)) (.cons (.cons (gN C (.q κ.castSucc)) (gN C (.q κ.succ))) (bodyTm C (Fin.castAdd K κ))))
    (fun κ => .cons (.c (num 1)) (.cons (gN C (.part κ)) (bodyTm C (Fin.natAdd K κ)))) p

/-- Instructions of a base party, with the diagonal. -/
noncomputable def basesTm (p : Fin (K + K)) : Tm := .cons (baseTm C p) (gN C (.dg p))

/-- The units given in a slot. -/
noncomputable def slotTm (z : M.Z) (a : Fin (K + K + A')) : Tm :=
  catTm ((G.allIds (K + K) U0 M.N U1).reverse.map fun id =>
    ifTm (C.nm (.slp (tab.kcons z id))) d1 (.c (listT [ofBits (C.key (a, id))])))

/-- Instruction of a role. -/
noncomputable def roleTm (r : M.R) : Tm :=
  .cons (.c (num (4 + tg r))) (.cons (gN C (.num r.1)) (.cons
    (listTm ((univ : Finset ((M.kind r.1).SlAt r.2)).toList.map fun e => slotTm C tab d1 ⟨r.1, e.1⟩ (M.rp r)))
    (listTm ((univ : Finset ((M.kind r.1).CnAt r.2)).toList.map fun ν =>
      gN C (.ch ⟨r.1, ν.1⟩ (decide ((M.kind r.1).c ν.1 ≠ r.2)))))))

/-- The content at a key. -/
def oneTm (k : List Bool) (id : G.Uid (K + K) U0 M.N U1) : Tm :=
  listTm [.cons (.c (num 3)) (.cons (.c (ofBits k)) (gN C (.cont id)))]

/-- Instruction for a unit in the end. -/
noncomputable def endTm (g : Fin mm) (id : G.Uid (K + K) U0 M.N U1) : Tm :=
  ifTm (C.nm (.slp (tab.kcur id))) d1
    (.ifeq (C.nm (.slp (tab.kgrp (G.hold0 M.np id)))) (gt g)
      (.ifeq (C.nm (.slp (tab.kgrp (G.hold1 M.np id)))) (gt g)
        (.c (listT [(Grp.Ins.both (C.key (G.hold0 M.np id, id)) (C.key (G.hold1 M.np id, id))).tree]))
        (oneTm C (C.key (G.hold0 M.np id, id)) id))
      (ifTm (C.nm (.slp (tab.kgrp (G.hold1 M.np id)))) (gt g) (oneTm C (C.key (G.hold1 M.np id, id)) id)))

/-- The script of a group. -/
noncomputable def scriptTm (g : Fin mm) : Tm :=
  .cons (.c (.cons (ofBits bT) (ofBits bub))) (catTm (
    (List.finRange (K + K)).map (fun p =>
      ifTm (C.nm (.slp (tab.kgrp (Fin.castAdd A' p)))) (gt g) (basesTm C p)) ++
    (Grp.allRoles M).map (fun r => ifTm (C.nm (.slp (tab.kgrp (M.rp r)))) (gt g) (listTm [roleTm C tab tg d1 r])) ++
    (G.allIds (K + K) U0 M.N U1).map (endTm C tab gt d1 g)))

end Templates

/-- The values in the end. -/
structure Final (C : Codes S M U0 U1 D pS) (tab : SlpTab P grp D pS) (qn : Q → ℕ) (pt : Fin K → Tree)
    (q : Fin (K + 1) → Q) (ρ : Option S → Fin (K + K) → RowData (K + K)) (n : NN K U0) (o : M.N → Fin U1)
    (b : G.Uid (K + K) U0 M.N U1 → UW ub) (st : NmT S M U0 U1 pS → Tree) : Prop where
  part : ∀ κ, st (.part κ) = pt κ
  q : ∀ a, st (.q a) = num (qn (q a))
  flag : ∀ s p, st (.flag s p) = flagT (ρ s p)
  kR : ∀ a b, st (.kR a b) = kRT C a b (n a b)
  kC : ∀ a b, st (.kC a b) = kCT C a b (n a b)
  dg : ∀ a, st (.dg a) = dgT C a (n a a)
  ch : ∀ ν d, st (.ch ν d) = chT C ν d (o ν)
  slp : ∀ k, st (.slp k) = C.dt (tab.fn k (n, o))
  num : ∀ x, st (.num x) = NS1.Tree.num (P.num n o x)
  cont : ∀ id v, b id = some v → st (.cont id) = ofBits (List.ofFn v)

section Expand

variable {C} {tab : SlpTab P grp D pS} {qn : Q → ℕ} {pt : Fin K → Tree} {q : Fin (K + 1) → Q}
  {ρ : Option S → Fin (K + K) → RowData (K + K)} {n : NN K U0} {o : M.N → Fin U1}
  {b : G.Uid (K + K) U0 M.N U1 → UW ub} {st : NmT S M U0 U1 pS → Tree} {tg : M.R → ℕ} {bT bub : List Bool}
  {cb : Option Γ → Fin c → Bool} {x : Fin K → List Γ}

theorem expand_gN (y : NmT S M U0 U1 pS) : (gN C y).expand (byPath C.nm st) = st y := byPath_nm C.nm_inj st y

theorem dt_inj : Function.Injective C.dt := by
  intro d d' h
  apply C.dc_inj
  rw [← path_ofBits (C.dc d), ← path_ofBits (C.dc d')]
  exact congrArg Tree.path h

variable (h : Final C tab qn pt q ρ n o b st)

include h

theorem expand_bodyTm (p : Fin (K + K)) :
    (bodyTm C p).expand (byPath C.nm st) = (Grp.bodyOf ρ n C.key C.dkey p).tree := by
  simp only [bodyTm, Tm.expand, expand_listTm, List.map_map, Function.comp_def, expand_gN, Grp.Body.tree, Grp.bodyOf,
    Grp.keysT, List.map_ofFn]
  congr 1
  · congr 1
    exact List.map_congr_left fun s _ => h.flag s p
  · congr 1
    · congr 2
      funext b'
      rw [h.kR]
      rfl
    · congr 2
      funext b'
      rw [h.kC]
      rfl

theorem expand_baseTm (hpt : ∀ κ, pt κ = listT (((x κ).map fun a => ofBits (List.ofFn (cb (some a)))).reverse))
    (p : Fin (K + K)) : (basesTm C p).expand (byPath C.nm st) =
      listT ((Grp.baseIns qn cb q x ρ n C.key C.dkey p).map Grp.Ins.tree) := by
  rw [basesTm, Tm.expand, Grp.baseIns, List.map_cons, expand_gN, h.dg]
  show _ = Tree.cons _ _
  congr 1
  · refine Fin.addCases (fun κ => ?_) (fun κ => ?_) p
    · rw [baseTm, Fin.addCases_left, Fin.addCases_left]
      simp only [Tm.expand, expand_gN, h.q, expand_bodyTm h, Grp.Ins.tree]
    · rw [baseTm, Fin.addCases_right, Fin.addCases_right]
      simp only [Tm.expand, expand_gN, h.part, expand_bodyTm h, Grp.Ins.tree, hpt, List.map_reverse, List.map_map,
        Function.comp_def]
  · rw [dgT, List.map_map]
    rfl

theorem expand_slotTm {d1 : Tree} (hd1 : ∀ d : Fin D, C.dt d = d1 ↔ d.1 = 1) (z : M.Z) (a : Fin (K + K + A')) :
    (slotTm C tab d1 z a).expand (byPath C.nm st) =
      listT ((((P.ids n o z).map fun id => C.key (a, id)).reverse).map ofBits) := by
  classical
  rw [slotTm, expand_catTm, List.flatMap_map]
  congr 1
  have e : ∀ id, ((ifTm (C.nm (.slp (tab.kcons z id))) d1 (.c (listT [ofBits (C.key (a, id))]))).expand
      (byPath C.nm st)).toList = if id ∈ P.cons n o z then [ofBits (C.key (a, id))] else [] := by
    intro id
    rw [expand_ifTm, byPath_nm C.nm_inj, h.slp]
    refine if_congr ?_ rfl rfl
    rw [hd1, tab.hcons]
    split_ifs with hc <;> simp [hc]
  simp only [e]
  rw [flatMap_if, flatMap_single, G.Plan.ids, ← List.map_reverse, ← List.filter_reverse, List.map_map]
  rfl

theorem expand_roleTm {d1 : Tree} (hd1 : ∀ d : Fin D, C.dt d = d1 ↔ d.1 = 1) (r : M.R) :
    (roleTm C tab tg d1 r).expand (byPath C.nm st) = (Grp.roleIns P n o C.key tg r).tree := by
  simp only [roleTm, Tm.expand, expand_listTm, List.map_map, Function.comp_def, expand_gN, h.num, Grp.roleIns,
    Grp.Ins.tree, Grp.keysT]
  congr 3
  · congr 1
    exact List.map_congr_left fun e _ => expand_slotTm h hd1 _ _
  · congr 1
    refine List.map_congr_left fun ν _ => ?_
    rw [h.ch]
    have hp : M.np ⟨r.1, ν.1⟩ (decide ((M.kind r.1).c ν.1 ≠ r.2)) = M.rp r := by
      obtain ⟨x', p⟩ := r
      obtain ⟨ν, hν⟩ := ν
      simp only [Sys.np, Sys.nr, Law.cnEnd, Sys.rp]
      by_cases hc : (M.kind x').c ν = p
      · simp [hc]
      · have hd : (M.kind x').d ν = p := hν.resolve_left hc
        simp [hc, hd]
    rw [chT, hp]

theorem expand_endTm {d1 : Tree} {gt : Fin mm → Tree} (hd1 : ∀ d : Fin D, C.dt d = d1 ↔ d.1 = 1)
    (hgt : ∀ (d : Fin D) g, C.dt d = gt g ↔ d.1 = g.1)
    (hb : ∀ id ∈ P.cur n o E, grp n o (G.hold0 M.np id) ≠ grp n o (G.hold1 M.np id) → b id ≠ none) (g : Fin mm)
    (id : G.Uid (K + K) U0 M.N U1) : ((endTm C tab gt d1 g id).expand (byPath C.nm st)).toList =
      (if id ∈ P.cur n o E then
        ((if grp n o (G.hold0 M.np id) = g then
          if grp n o (G.hold1 M.np id) = g then some (Grp.Ins.both (C.key (G.hold0 M.np id, id)) (C.key (G.hold1 M.np id, id)))
          else some (.one (C.key (G.hold0 M.np id, id)) (uwBits (b id)))
        else if grp n o (G.hold1 M.np id) = g then some (.one (C.key (G.hold1 M.np id, id)) (uwBits (b id)))
        else none).map Grp.Ins.tree).toList else []) := by
  classical
  have hslp : ∀ k, byPath C.nm st (C.nm (.slp k)) = C.dt (tab.fn k (n, o)) := fun k => by
    rw [byPath_nm C.nm_inj, h.slp]
  have hg : ∀ p, (C.dt (tab.fn (tab.kgrp p) (n, o)) = gt g ↔ grp n o p = g) := by
    intro p
    rw [hgt, tab.hgrp]
    exact Fin.ext_iff.symm
  have hone : ∀ k, b id ≠ none → (oneTm C k id).expand (byPath C.nm st) = listT [(Grp.Ins.one k (uwBits (b id))).tree] := by
    intro k hbn
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hbn
    simp only [oneTm, expand_listTm, List.map_cons, List.map_nil, Tm.expand, expand_gN, h.cont id v hv, Grp.Ins.tree, hv,
      uwBits]
  rw [endTm, expand_ifTm, hslp]
  have hcur : C.dt (tab.fn (tab.kcur id) (n, o)) = d1 ↔ id ∈ P.cur n o E := by
    rw [hd1, tab.hcur]
    split_ifs with hc <;> simp [hc]
  by_cases hc : id ∈ P.cur n o E
  swap
  · rw [if_neg fun h' => hc (hcur.1 h'), if_neg hc]
  rw [if_pos (hcur.2 hc), if_pos hc]
  simp only [Tm.expand, hslp]
  by_cases h0 : grp n o (G.hold0 M.np id) = g
  · rw [if_pos ((hg _).2 h0), if_pos h0]
    by_cases h1 : grp n o (G.hold1 M.np id) = g
    · rw [if_pos ((hg _).2 h1), if_pos h1]
      rfl
    · rw [if_neg fun h' => h1 ((hg _).1 h'), if_neg h1, hone _ (hb id hc fun h' => h1 (h' ▸ h0))]
      simp
  · rw [if_neg fun h' => h0 ((hg _).1 h'), if_neg h0]
    rw [expand_ifTm, hslp]
    by_cases h1 : grp n o (G.hold1 M.np id) = g
    · rw [if_pos ((hg _).2 h1), if_pos h1, hone _ (hb id hc fun h' => h0 (h'.trans h1))]
      simp
    · rw [if_neg fun h' => h1 ((hg _).1 h'), if_neg h1]
      rfl

/-- **The script of a group.** -/
theorem expand_scriptTm {d1 : Tree} {gt : Fin mm → Tree} (hd1 : ∀ d : Fin D, C.dt d = d1 ↔ d.1 = 1)
    (hgt : ∀ (d : Fin D) g, C.dt d = gt g ↔ d.1 = g.1)
    (hpt : ∀ κ, pt κ = listT (((x κ).map fun a => ofBits (List.ofFn (cb (some a)))).reverse))
    (hb : ∀ id ∈ P.cur n o E, grp n o (G.hold0 M.np id) ≠ grp n o (G.hold1 M.np id) → b id ≠ none) (g : Fin mm) :
    (scriptTm C tab tg bT bub gt d1 g).expand (byPath C.nm st) =
      Grp.scriptT bT bub (Grp.script qn cb P q x ρ n o (grp n o) g C.key C.dkey tg b) := by
  classical
  have hslp : ∀ k, byPath C.nm st (C.nm (.slp k)) = C.dt (tab.fn k (n, o)) := fun k => by
    rw [byPath_nm C.nm_inj, h.slp]
  have hg : ∀ p, (C.dt (tab.fn (tab.kgrp p) (n, o)) = gt g ↔ grp n o p = g) := by
    intro p
    rw [hgt, tab.hgrp]
    exact Fin.ext_iff.symm
  rw [scriptTm, Tm.expand, Tm.expand, Grp.scriptT, expand_catTm]
  congr 2
  rw [Grp.script, List.flatMap_append, List.flatMap_append, List.map_append, List.map_append, List.flatMap_map,
    List.flatMap_map, List.flatMap_map]
  congr 1
  · congr 1
    · have e : ∀ p : Fin (K + K), ((ifTm (C.nm (.slp (tab.kgrp (Fin.castAdd A' p)))) (gt g) (basesTm C p)).expand
          (byPath C.nm st)).toList = if grp n o (Fin.castAdd A' p) = g then
          (Grp.baseIns qn cb q x ρ n C.key C.dkey p).map Grp.Ins.tree else [] := by
        intro p
        rw [expand_ifTm, hslp, expand_baseTm h hpt, toList_listT]
        exact if_congr (hg _) rfl rfl
      simp only [e]
      rw [flatMap_if, Grp.baseList, List.map_flatMap]
    · have e : ∀ r : M.R, ((ifTm (C.nm (.slp (tab.kgrp (M.rp r)))) (gt g) (listTm [roleTm C tab tg d1 r])).expand
          (byPath C.nm st)).toList = if grp n o (M.rp r) = g then [(Grp.roleIns P n o C.key tg r).tree] else [] := by
        intro r
        rw [expand_ifTm, hslp, expand_listTm, toList_listT]
        refine if_congr (hg _) ?_ rfl
        simp [expand_roleTm h hd1]
      simp only [e]
      rw [flatMap_if, flatMap_single, Grp.roleList, List.map_map]
      rfl
  · simp only [expand_endTm h hd1 hgt hb]
    rw [Grp.endIns]
    generalize G.allIds (K + K) U0 M.N U1 = l
    induction l with
    | nil => rfl
    | cons id l ih =>
      rw [List.flatMap_cons, ih]
      by_cases hc : id ∈ P.cur n o E
      · simp only [hc, if_true, List.filter_cons_of_pos, decide_true, List.filterMap_cons]
        cases (if grp n o (G.hold0 M.np id) = g then
          if grp n o (G.hold1 M.np id) = g then some (Grp.Ins.both (C.key (G.hold0 M.np id, id)) (C.key (G.hold1 M.np id, id)))
          else some (.one (C.key (G.hold0 M.np id, id)) (uwBits (b id)))
        else if grp n o (G.hold1 M.np id) = g then some (.one (C.key (G.hold1 M.np id, id)) (uwBits (b id)))
        else none) <;> simp
      · simp [hc]

end Expand

end Nc.Dl
