/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Dl.Cut
import NS1.Guess

/-!
# The size of the dealing program
-/

set_option linter.unusedSectionVars false

namespace Nc.Dl

open NS1 NS1.Tree Finset Nc.G Nc.Cut Codes

namespace Sz

theorem size_quote (c : Tree) : (Fm.quote c).code.size = c.size + 2 := by
  simp only [Fm.code, Tree.size, size_num]; ring

theorem size_id : Fm.id.code.size = 5 := by
  simp only [Fm.code, Tree.size, size_num]

theorem size_hd (a : Fm) : (Fm.hd a).code.size = a.code.size + 6 := by
  simp only [Fm.code, Tree.size, size_num]; ring

theorem size_tl (a : Fm) : (Fm.tl a).code.size = a.code.size + 8 := by
  simp only [Fm.code, Tree.size, size_num]; ring

theorem size_cons (a b : Fm) : (Fm.cons a b).code.size = a.code.size + b.code.size + 11 := by
  simp only [Fm.code, Tree.size, size_num]; ring

theorem size_ite (a b c : Fm) : (Fm.ite a b c).code.size = a.code.size + b.code.size + c.code.size + 14 := by
  simp only [Fm.code, Tree.size, size_num]; ring

theorem size_run (a b : Fm) : (Fm.run a b).code.size = a.code.size + b.code.size + 15 := by
  simp only [Fm.code, Tree.size, size_num]; ring

theorem size_app (p : Tree) (e : Fm) : (app p e).code.size = p.size + e.code.size + 17 := by
  rw [app, size_run, size_quote]; ring

theorem size_lett (e b : Fm) : (lett e b).code.size = b.code.size + e.code.size + 17 := by
  rw [lett, size_run, size_quote]; ring

theorem size_foldF (step s l : Fm) : (foldF step s l).code.size ≤ 2 * step.code.size + s.code.size + l.code.size + 500 := by
  rw [foldF, size_app, size_cons, size_cons, size_quote, foldB, size_ite, size_run, size_cons, size_cons, size_lett,
    size_cons]
  simp only [size_hd, size_tl, size_id]
  omega

theorem size_mapF (step s l : Fm) : (mapF step s l).code.size ≤ 2 * step.code.size + s.code.size + l.code.size + 600 := by
  rw [mapF, size_app, size_cons, size_cons, size_quote, mapB, size_ite, size_cons, size_lett, size_cons, size_run,
    size_cons, size_cons]
  simp only [size_hd, size_tl, size_id, size_quote, Tree.size]
  omega

theorem size_listT (l : List Tree) : (listT l).size = (l.map Tree.size).sum + l.length + 1 := by
  induction l with
  | nil => rfl
  | cons t l ih => simp only [listT, Tree.size, ih, List.map_cons, List.sum_cons, List.length_cons]; ring

theorem sum_le {α : Type*} {l : List α} {f : α → ℕ} {n b : ℕ} (hl : l.length ≤ n) (hb : ∀ t ∈ l, f t ≤ b) :
    (l.map f).sum ≤ n * b := by
  have h : (l.map f).sum ≤ l.length * b := by
    clear hl
    induction l with
    | nil => simp
    | cons t l ih =>
      have h1 := hb t List.mem_cons_self
      have h2 := ih fun t ht => hb t (List.mem_cons_of_mem _ ht)
      rw [List.map_cons, List.sum_cons, List.length_cons, add_mul, one_mul]
      omega
  exact h.trans (Nat.mul_le_mul_right _ hl)

theorem size_listT_le {l : List Tree} {n b : ℕ} (hl : l.length ≤ n) (hb : ∀ t ∈ l, t.size ≤ b) :
    (listT l).size ≤ n * (b + 1) + 1 := by
  have h := sum_le hl hb
  rw [size_listT, mul_add, mul_one]
  omega

theorem size_c (t : Tree) : (Tm.c t).tree.size = t.size + 2 := by
  simp only [Tm.tree, Tree.size, size_num]; ring

theorem size_get (p : List Bool) : (Tm.get p).tree.size = (ofBits p).size + 4 := by
  simp only [Tm.tree, Tree.size, size_num]; ring

theorem size_tmCons (a b : Tm) : (Tm.cons a b).tree.size = a.tree.size + b.tree.size + 7 := by
  simp only [Tm.tree, Tree.size, size_num]; ring

theorem size_ifeq (p : List Bool) (t : Tree) (a b : Tm) :
    (Tm.ifeq p t a b).tree.size = (ofBits p).size + t.size + a.tree.size + b.tree.size + 11 := by
  simp only [Tm.tree, Tree.size, size_num]; ring

theorem size_tmApp (a b : Tm) : (Tm.app a b).tree.size = a.tree.size + b.tree.size + 11 := by
  simp only [Tm.tree, Tree.size, size_num]; ring

theorem size_ifTm (p : List Bool) (t : Tree) (a : Tm) :
    (ifTm p t a).tree.size = (ofBits p).size + t.size + a.tree.size + 14 := by
  rw [ifTm, size_ifeq, size_c]
  simp only [Tree.size]

theorem size_listTm (ts : List Tm) : (listTm ts).tree.size = (ts.map fun t => t.tree.size).sum + 7 * ts.length + 3 := by
  induction ts with
  | nil => rfl
  | cons t ts ih => rw [listTm, size_tmCons, ih, List.map_cons, List.sum_cons, List.length_cons]; ring

theorem size_listTm_le {ts : List Tm} {n b : ℕ} (hl : ts.length ≤ n) (hb : ∀ t ∈ ts, t.tree.size ≤ b) :
    (listTm ts).tree.size ≤ n * (b + 7) + 3 := by
  have h := sum_le hl hb
  rw [size_listTm, mul_add]
  omega

theorem size_catTm (ts : List Tm) : (catTm ts).tree.size = (ts.map fun t => t.tree.size).sum + 11 * ts.length + 3 := by
  induction ts with
  | nil => rfl
  | cons t ts ih => rw [catTm, size_tmApp, ih, List.map_cons, List.sum_cons, List.length_cons]; ring

theorem size_catTm_le {ts : List Tm} {n b : ℕ} (hl : ts.length ≤ n) (hb : ∀ t ∈ ts, t.tree.size ≤ b) :
    (catTm ts).tree.size ≤ n * (b + 11) + 3 := by
  have h := sum_le hl hb
  rw [size_catTm, mul_add]
  omega

theorem size_bits {w : List Bool} {L : ℕ} (h : w.length ≤ L) : (ofBits w).size ≤ 4 * L + 1 :=
  (size_ofBits w).trans (by omega)

theorem size_bit (b : Bool) : (bit b).size ≤ 3 := by cases b <;> simp [bit, one, Tree.size]

theorem size_pick (p : List Bool) (t : Tree) : (DStep.pick p t).tree.size = (ofBits p).size + t.size + 3 := by
  simp only [DStep.tree, Tree.size, size_num]; ring

theorem size_op (p q d : List Bool) (φ : Tree) : (DStep.op p q d φ).tree.size =
    (ofBits p).size + (ofBits q).size + (ofBits d).size + φ.size + 7 := by
  simp only [DStep.tree, Tree.size, size_num]; ring

theorem size_dbits (p d : List Bool) : (DStep.bits p d).tree.size = (ofBits p).size + (ofBits d).size + 7 := by
  simp only [DStep.tree, Tree.size, size_num]; ring

theorem size_check (p : List Bool) : (DStep.check p).tree.size = (ofBits p).size + 8 := by
  simp only [DStep.tree, Tree.size, size_num]; ring

end Sz

open Sz

section formulas

/-- The size of the fixed parts of the program. -/
def dealC : ℕ := 4 * (dstepF []).code.size + 2 * partStep.code.size + 2 * (wordB .nil .nil).code.size +
  2 * (tmF (.tl .id) (.hd .id)).code.size + 5000

theorem size_dstepF (n : List Bool) : (dstepF n).code.size + 1 = (dstepF []).code.size + (ofBits n).size := by
  have h : ∀ n, (bitsF n).code.size = 2 * bitsB.code.size + (ofBits n).size + 22 := by
    intro n
    rw [bitsF, size_app, size_quote]
    simp only [Tree.size]
    ring
  simp only [dstepF, size_ite, size_lett, size_cons, h]
  have : (ofBits []).size = 1 := rfl
  rw [this]
  ring

theorem size_wordB (t0 t1 : Tree) : (wordB t0 t1).code.size + 2 = (wordB .nil .nil).code.size + t0.size + t1.size := by
  simp only [wordB, size_ite, size_cons, size_quote, Tree.size]
  ring

/-- The size of the dealing program, by its lists. -/
theorem size_dealF (t0 t1 : Tree) (names : List (List Bool)) (nl nub : List Bool) (sts sts' : List DStep) (ts : List Tm) :
    (dealF t0 t1 names nl nub sts sts' ts).code.size ≤ dealC + 4 * (ofBits nub).size + (ofBits nl).size +
      2 * t0.size + 2 * t1.size + (listT (names.map ofBits)).size + (listT (sts.map DStep.tree)).size +
      (listT (sts'.map DStep.tree)).size + (listT (ts.map Tm.tree)).size := by
  have h7 : (wordF t0 t1 .id).code.size = 2 * (wordB t0 t1).code.size + 49 := by
    rw [wordF, size_app, size_cons, size_cons, size_quote, size_quote, size_id]
    simp only [Tree.size]
    ring
  have h1 : (dstepsF nub sts (partsF names nl (wordF t0 t1 .id))).code.size ≤ 2 * (dstepF nub).code.size +
      (partsF names nl (wordF t0 t1 .id)).code.size + ((listT (sts.map DStep.tree)).size + 2) + 500 := by
    rw [dstepsF, ← size_quote]
    exact size_foldF _ _ _
  have h2 : (dstepsF nub sts' .id).code.size ≤ 2 * (dstepF nub).code.size + 5 +
      ((listT (sts'.map DStep.tree)).size + 2) + 500 := by
    rw [dstepsF, ← size_quote, ← size_id]
    exact size_foldF _ _ _
  have h3 : (tmsF ts .id).code.size ≤ 2 * (tmF (.tl .id) (.hd .id)).code.size + 5 +
      ((listT (ts.map Tm.tree)).size + 2) + 600 := by
    rw [tmsF, ← size_quote, ← size_id]
    exact size_mapF _ _ _
  have h4 : (partsF names nl (wordF t0 t1 .id)).code.size ≤ 2 * partStep.code.size +
      (1 + 2 + ((ofBits nl).size + 2 + (2 * (wordB t0 t1).code.size + 49) + 11) + 11) +
      ((listT (names.map ofBits)).size + 2) + 500 + 6 := by
    rw [partsF, size_hd, ← h7]
    have := size_foldF partStep (.cons (.quote .nil) (.cons (.quote (ofBits nl)) (wordF t0 t1 .id)))
      (.quote (listT (names.map ofBits)))
    rw [size_cons, size_cons, size_quote, size_quote, size_quote] at this
    simp only [Tree.size] at this
    exact Nat.add_le_add_right this 6
  have h5 := size_dstepF nub
  have h6 := size_wordB t0 t1
  have h8 : dealC = 4 * (dstepF []).code.size + 2 * partStep.code.size + 2 * (wordB .nil .nil).code.size +
    2 * (tmF (.tl .id) (.hd .id)).code.size + 5000 := rfl
  rw [dealF, size_lett, size_lett, h8]
  generalize (dstepsF nub sts (partsF names nl (wordF t0 t1 .id))).code.size = a1 at *
  generalize (dstepsF nub sts' .id).code.size = a2 at *
  generalize (tmsF ts .id).code.size = a3 at *
  generalize (partsF names nl (wordF t0 t1 .id)).code.size = a4 at *
  generalize (dstepF nub).code.size = a5 at *
  generalize (dstepF []).code.size = a6 at *
  generalize (wordB t0 t1).code.size = a7 at *
  generalize (wordB .nil .nil).code.size = a8 at *
  generalize (tmF (.tl .id) (.hd .id)).code.size = a9 at *
  generalize partStep.code.size = a10 at *
  omega

end formulas

variable {A : Type} [CommRing A] {Γ S Q : Type} [Fintype Γ] [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q]
  [DecidableEq Q] {K A' E U0 U1 mm D pS c : ℕ} {M : Sys A (K + K + A') E} {P : G.Plan M U0 U1}
  {grp : NN K U0 → (M.N → Fin U1) → Fin (K + K + A') → Fin mm} (C : Codes S M U0 U1 D pS) (tab : SlpTab P grp D pS)
  (qn : Q → ℕ) (tg : M.R → ℕ) (bT bub nl nub : List Bool) (gt : Fin mm → Tree) (d1 gp : Tree) (cb : Option Γ → Fin c → Bool)
  (b0 b1 : Γ) (i e : Q) (hU0 : U0 < D) (hU1 : U1 ≤ D)

/-- What bounds the sizes. -/
structure SizeHyp (X Lc : ℕ) : Prop where
  hLc : 1 ≤ Lc
  nm : ∀ y, (C.nm y).length ≤ Lc
  dc : ∀ d, (C.dc d).length ≤ Lc
  rc : ∀ d, (C.rc d).length ≤ Lc
  key : ∀ y, (C.key y).length ≤ Lc
  dkey : ∀ y, (C.dkey y).length ≤ Lc
  hK1 : K + 1 ≤ X
  hK2 : K + K ≤ X
  hU0 : U0 + 1 ≤ X
  hU1 : U1 ≤ X
  hE : E + 1 ≤ X
  hD : D ≤ X
  hpS : pS ≤ X
  hN : Fintype.card M.N ≤ X
  hId : Fintype.card (G.Uid (K + K) U0 M.N U1) ≤ X
  hS : Fintype.card (Option S) ≤ X
  hQ : Fintype.card Q + 1 ≤ X
  row : Fintype.card (RowData (K + K)) ≤ X
  hR : Fintype.card M.R ≤ X
  Sl : ∀ r : M.R, Fintype.card ((M.kind r.1).SlAt r.2) ≤ X
  Cn : ∀ r : M.R, Fintype.card ((M.kind r.1).CnAt r.2) ≤ X
  hqn : ∀ q, qn q ≤ X
  htg : ∀ r, tg r + 4 ≤ X

section sizes

variable {C} {qn} {tg} {X Lc : ℕ} (H : SizeHyp C qn tg X Lc)

include H

theorem SizeHyp.X1 : 1 ≤ X := (Nat.le_add_left 1 K).trans H.hK1

theorem SizeHyp.facts : X ≤ X * Lc ∧ Lc ≤ X * Lc ∧ X * Lc ≤ (X * Lc) ^ 2 ∧ 1 ≤ X * Lc ∧ X * (X * Lc) ≤ (X * Lc) ^ 2 := by
  have h1 := H.X1
  have h2 := H.hLc
  have h3 : 1 ≤ X * Lc := Nat.mul_le_mul h1 h2
  refine ⟨Nat.le_mul_of_pos_right _ h2, Nat.le_mul_of_pos_left _ h1, ?_, h3, ?_⟩
  · rw [pow_two]
    exact Nat.le_mul_of_pos_right _ h3
  · rw [pow_two]
    exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ h2)

/-- A step that chooses. -/
theorem size_pickS {α : Type} {opts : List α} {o : α → List (NmT S M U0 U1 pS × Tree)} (hopts : opts.length ≤ X)
    (ho : ∀ a ∈ opts, (o a).length ≤ 4 ∧ ∀ b ∈ o a, b.2.size ≤ 19 * (X * Lc)) :
    (pickS C opts o).tree.size ≤ 120 * (X * Lc) ^ 2 := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := H.facts
  have h1 : ∀ t ∈ opts.map fun a => optT C.nm (o a), t.size ≤ 105 * (X * Lc) := by
    intro t ht
    rw [List.mem_map] at ht
    obtain ⟨a, ha, rfl⟩ := ht
    obtain ⟨h2, h3⟩ := ho a ha
    refine (size_listT_le (n := 4) (b := 25 * (X * Lc)) (by rw [List.length_map]; exact h2) ?_).trans (by omega)
    intro t ht
    rw [List.mem_map] at ht
    obtain ⟨b, hb, rfl⟩ := ht
    have h4 := h3 b hb
    have h5 := size_bits (H.nm b.1)
    simp only [Tree.size]
    omega
  have h2 := size_listT_le (n := X) (b := 105 * (X * Lc)) (by rw [List.length_map]; exact hopts) h1
  have h3 := size_bits (H.nm .zero)
  rw [pickS, size_pick]
  simp only [Tree.size]
  have h4 : X * (105 * (X * Lc) + 1) = 105 * (X * (X * Lc)) + X := by ring
  omega

theorem size_dt (d : Fin D) : (C.dt d).size ≤ 4 * Lc + 1 := size_bits (H.dc d)

theorem size_opS (x y z : NmT S M U0 U1 pS) {φ : Tree} (hφ : φ.size ≤ 60 * (X * Lc) ^ 2) :
    (DStep.op (C.nm x) (C.nm y) (C.nm z) φ).tree.size ≤ 120 * (X * Lc) ^ 2 := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := H.facts
  have h1 := size_bits (H.nm x)
  have h2 := size_bits (H.nm y)
  have h3 := size_bits (H.nm z)
  rw [size_op]
  omega

theorem size_un (x z : NmT S M U0 U1 pS) {f : Fin D → Tree} (hf : ∀ d, (f d).size ≤ 5 * (X * Lc)) :
    (C.un x z f).tree.size ≤ 120 * (X * Lc) ^ 2 := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := H.facts
  refine size_opS H _ _ _ ?_
  have h := size_trieOf_le (code := C.dc) (f := fun d => Tree.cons (f d) .nil) (L := Lc) (s := 7 * (X * Lc)) H.dc
    fun d => by
      have := hf d
      simp only [Tree.size]
      omega
  rw [Fintype.card_fin] at h
  have h2 := Nat.mul_le_mul_right (7 * (X * Lc) + 4 * Lc + 4) H.hD
  have h3 : X * (7 * (X * Lc) + 4 * Lc + 4) = 7 * (X * (X * Lc)) + 4 * (X * Lc) + 4 * X := by ring
  omega

theorem size_con (z : NmT S M U0 U1 pS) {t : Tree} (ht : t.size ≤ 5 * (X * Lc)) :
    (C.con z t).tree.size ≤ 120 * (X * Lc) ^ 2 := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := H.facts
  refine size_opS H _ _ _ ?_
  simp only [Tree.size]
  omega

theorem size_trie2 {α : Type} [Fintype α] {code : α → List Bool} (hc : ∀ a, (code a).length ≤ Lc)
    (hα : Fintype.card α ≤ X) {f : α → α → Tree} (hf : ∀ a b, (f a b).size ≤ 4 * Lc + 1) :
    (trieOf code fun a => trieOf code fun b => f a b).size ≤ 50 * (X * Lc) ^ 2 := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := H.facts
  have h1 : ∀ a, (trieOf code fun b => f a b).size ≤ 13 * (X * Lc) + 1 := by
    intro a
    have h := size_trieOf_le (code := code) (f := fun b => f a b) (L := Lc) hc (hf a)
    have h2 := Nat.mul_le_mul_right (4 * Lc + 1 + 4 * Lc + 4) hα
    have h3 : X * (4 * Lc + 1 + 4 * Lc + 4) = 8 * (X * Lc) + 5 * X := by ring
    omega
  have h := size_trieOf_le (code := code) (f := fun a => trieOf code fun b => f a b) (L := Lc) hc h1
  have h2 := Nat.mul_le_mul_right (13 * (X * Lc) + 1 + 4 * Lc + 4) hα
  have h3 : X * (13 * (X * Lc) + 1 + 4 * Lc + 4) = 13 * (X * (X * Lc)) + 4 * (X * Lc) + 5 * X := by ring
  omega

/-- The keys of units. -/
theorem size_keysL {α : Type} {l : List α} {f : α → List Bool} (hl : l.length ≤ X) (hf : ∀ a, (f a).length ≤ Lc) :
    (listT (l.map fun a => ofBits (f a))).size ≤ 19 * (X * Lc) := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := H.facts
  refine (size_listT_le (n := X) (b := 4 * Lc + 1) (by rw [List.length_map]; exact hl) ?_).trans ?_
  · intro t ht
    rw [List.mem_map] at ht
    obtain ⟨a, -, rfl⟩ := ht
    exact size_bits (hf a)
  · have : X * (4 * Lc + 1 + 1) = 4 * (X * Lc) + 2 * X := by ring
    omega

theorem length_filter_finRange {n : ℕ} (hn : n ≤ X) (p : Fin n → Bool) : ((List.finRange n).filter p).length ≤ X := by
  have := List.length_filter_le p (List.finRange n)
  rw [List.length_finRange] at this
  omega

/-- Every step is small. -/
theorem size_steps18 : ∀ st ∈ steps18 C tab qn i e hU0 hU1, st.tree.size ≤ 120 * (X * Lc) ^ 2 := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := H.facts
  have hX1 := H.X1
  have hLc := H.hLc
  have hUX : U0 ≤ X := (Nat.le_succ _).trans H.hU0
  have hdt : ∀ d, (C.dt d).size ≤ 5 * (X * Lc) := fun d => (size_dt H d).trans (by omega)
  have hbit : ∀ b : Bool, (bit b).size ≤ 5 * (X * Lc) := fun b => (size_bit b).trans (by omega)
  intro st hst
  simp only [steps18, List.mem_append] at hst
  rcases hst with h | h | h | h | (h | h | h) | h
  · rw [steps1, List.mem_map] at h
    obtain ⟨a, -, rfl⟩ := h
    refine size_pickS H ?_ fun q _ => ⟨by simp, fun b hb => ?_⟩
    · have hQ := H.hQ
      unfold opts1
      split_ifs
      · simpa using hX1
      · simpa using hX1
      · rw [Finset.length_toList, Finset.card_univ]; omega
    · rw [List.mem_singleton] at hb
      subst hb
      have := H.hqn q
      simp only [size_num]
      omega
  · rw [steps2, List.mem_map] at h
    obtain ⟨a, -, rfl⟩ := h
    refine size_pickS H (by rw [Finset.length_toList, Finset.card_univ]; exact H.row) fun d _ => ⟨by simp, fun b hb => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl
    · simp only [flagT]
      refine (size_listT_le (n := X) (b := 5) (by simpa using H.hK2) ?_).trans (by omega)
      intro t ht
      rw [List.mem_map] at ht
      obtain ⟨k, hk, rfl⟩ := ht
      rw [List.mem_reverse, List.mem_ofFn] at hk
      obtain ⟨b, rfl⟩ := hk
      rw [size_num]
      unfold Grp.rowFlag
      split_ifs <;> omega
    · have := size_bits (H.rc d)
      simp only
      omega
  · rw [steps3, List.mem_map] at h
    obtain ⟨a, -, rfl⟩ := h
    refine size_pickS H (by rw [Finset.length_toList, Finset.card_univ, Fintype.card_fin]; exact H.hU0) fun n _ => ⟨?_, ?_⟩
    · simp only [o3, List.length_cons]
      split_ifs <;> simp
    · intro b hb
      simp only [o3, List.mem_cons] at hb
      rcases hb with rfl | rfl | rfl | hb
      · exact size_keysL H (length_filter_finRange H hUX _) fun k => H.key _
      · refine size_keysL H (length_filter_finRange H hUX _) fun k => ?_
        split_ifs
        · exact H.dkey _
        · exact H.key _
      · have := hdt (digN hU0 n)
        simp only
        omega
      · split_ifs at hb
        · rw [List.mem_singleton] at hb
          subst hb
          simp only [dgT]
          refine (size_listT_le (n := X) (b := 8 * Lc + 9) (by
            rw [List.length_map]; exact length_filter_finRange H hUX _) ?_).trans ?_
          · intro t ht
            rw [List.mem_map] at ht
            obtain ⟨k, -, rfl⟩ := ht
            have k1 := size_bits (H.key (Fin.castAdd A' a.1, .init a.1 a.1 k))
            have k2 := size_bits (H.dkey (a.1, k))
            simp only [Grp.Ins.tree, Tree.size, size_num]
            omega
          · have : X * (8 * Lc + 9 + 1) = 8 * (X * Lc) + 10 * X := by ring
            omega
        · simp at hb
  · rw [steps4, List.mem_map] at h
    obtain ⟨ν, -, rfl⟩ := h
    refine size_pickS H (by rw [Finset.length_toList, Finset.card_univ, Fintype.card_fin]; exact H.hU1) fun j _ => ⟨by simp, ?_⟩
    intro b hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · have := hdt (digO hU1 j)
      simp only
      omega
    · exact size_keysL H (length_filter_finRange H H.hU1 _) fun k => H.key _
    · exact size_keysL H (length_filter_finRange H H.hU1 _) fun k => H.key _
  · rw [steps5, List.mem_map] at h
    obtain ⟨a, -, rfl⟩ := h
    have hb : ∀ b : Bool, (bit b).size ≤ 4 * Lc + 1 := fun b => (size_bit b).trans (by omega)
    unfold rowStep
    split_ifs
    · have hb3 : ∀ f : RowData (K + K) → Tree, (∀ d, (f d).size ≤ 3) →
          (Tree.cons (trieOf C.rc f) .nil).size ≤ 60 * (X * Lc) ^ 2 := by
        intro f hf
        have h := size_trieOf_le (code := C.rc) (f := f) (L := Lc) (s := 3) H.rc hf
        have h2 := Nat.mul_le_mul_right (3 + 4 * Lc + 4) H.row
        have h3 : X * (3 + 4 * Lc + 4) = 4 * (X * Lc) + 7 * X := by ring
        simp only [Tree.size]
        omega
      exact size_opS H _ _ _ (hb3 _ fun d => size_bit _)
    · refine size_opS H _ _ _ ((size_trie2 H H.rc H.row fun d' d => hb _).trans (by omega))
  · rw [steps6, List.mem_map] at h
    obtain ⟨k, -, rfl⟩ := h
    unfold slpStep
    split_ifs with h1 h2 h3
    · exact size_un H _ _ hdt
    · exact size_con H _ (hdt _)
    · refine size_opS H _ _ _ ((size_trie2 H H.dc (by rw [Fintype.card_fin]; exact H.hD) fun d d' => size_dt H _).trans
        (by omega))
    · refine size_con H _ ?_
      simp only [Tree.size]
      omega
  · rw [steps7, List.mem_map] at h
    obtain ⟨a, -, rfl⟩ := h
    rcases a with y | c | id
    · refine size_un H _ _ fun d => ?_
      have h1 := H.hD
      have h2 := d.2
      rw [size_num]
      omega
    · exact size_un H _ _ fun d => hbit _
    · exact size_un H _ _ fun d => hbit _
  · rw [steps8, List.map_append, List.mem_append, List.map_map, List.map_map, List.mem_map, List.mem_map] at h
    rcases h with ⟨a, -, rfl⟩ | ⟨c, -, rfl⟩
    · have := size_bits (H.nm (.row a.1 a.2))
      simp only [Function.comp_apply, size_check]
      omega
    · have := size_bits (H.nm (.cond c))
      simp only [Function.comp_apply, size_check]
      omega

theorem length_steps18 : (steps18 C tab qn i e hU0 hU1).length ≤ 11 * X ^ 2 := by
  have hX1 := H.X1
  have hX2 : X ≤ X ^ 2 := Nat.le_self_pow (by norm_num) X
  have hK1 := H.hK1
  have hN := H.hN
  have hE := H.hE
  have hId := H.hId
  have hp := H.hpS
  have hSK : Fintype.card (Option S) * (K + K) ≤ X ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul H.hS H.hK2
  have hKK : (K + K) * (K + K) ≤ X ^ 2 := by
    rw [pow_two]
    exact Nat.mul_le_mul H.hK2 H.hK2
  have l2 : (univ : Finset (Option S × Fin (K + K))).toList.length = Fintype.card (Option S) * (K + K) := by
    rw [Finset.length_toList, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  have l3 : (univ : Finset (Fin (K + K) × Fin (K + K))).toList.length = (K + K) * (K + K) := by
    rw [Finset.length_toList, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  have l7 : (univ : Finset (Ix7 M U0 U1)).toList.length = E + (E + 1 + Fintype.card (G.Uid (K + K) U0 M.N U1)) := by
    rw [Finset.length_toList, Finset.card_univ, Fintype.card_sum, Fintype.card_sum, Fintype.card_option, Fintype.card_fin]
  simp only [steps18, steps1, steps2, steps3, steps4, steps5, steps6, steps7, steps8, List.length_append, List.length_map,
    l2, l3, l7, List.length_finRange]
  simp only [Finset.length_toList, Finset.card_univ, Fintype.card_fin, Fintype.card_option] at hSK ⊢
  omega

theorem size_gN (y : NmT S M U0 U1 pS) : (gN C y).tree.size ≤ 4 * Lc + 5 := by
  have := size_bits (H.nm y)
  rw [gN, size_get]
  omega

theorem size_bodyTm (p : Fin (K + K)) : (bodyTm C p).tree.size ≤ 75 * (X * Lc) := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := H.facts
  have h : ∀ l : List Tm, l.length ≤ X → (∀ t ∈ l, t.tree.size ≤ 4 * Lc + 5) → (listTm l).tree.size ≤ 19 * (X * Lc) := by
    intro l hl hb
    refine (size_listTm_le hl hb).trans ?_
    have : X * (4 * Lc + 5 + 7) = 4 * (X * Lc) + 12 * X := by ring
    omega
  have h1 := h ((univ : Finset (Option S)).toList.map fun s => gN C (.flag s p)) (by
    rw [List.length_map, Finset.length_toList, Finset.card_univ]; exact H.hS) (by
      intro t ht
      rw [List.mem_map] at ht
      obtain ⟨s, -, rfl⟩ := ht
      exact size_gN H _)
  have h2 := h (List.ofFn fun b => gN C (.kR p b)) (by rw [List.length_ofFn]; exact H.hK2) (by
      intro t ht
      rw [List.mem_ofFn] at ht
      obtain ⟨s, rfl⟩ := ht
      exact size_gN H _)
  have h3 := h (List.ofFn fun b => gN C (.kC b p)) (by rw [List.length_ofFn]; exact H.hK2) (by
      intro t ht
      rw [List.mem_ofFn] at ht
      obtain ⟨s, rfl⟩ := ht
      exact size_gN H _)
  rw [bodyTm, size_tmCons, size_tmCons]
  omega

theorem size_baseTm (p : Fin (K + K)) : (baseTm C p).tree.size ≤ 120 * (X * Lc) := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := H.facts
  unfold baseTm
  refine Fin.addCases (fun κ => ?_) (fun κ => ?_) p
  · rw [Fin.addCases_left, size_tmCons, size_tmCons, size_tmCons, size_c]
    have h1 := size_gN H (.q κ.castSucc)
    have h2 := size_gN H (.q κ.succ)
    have h3 := size_bodyTm H (Fin.castAdd K κ)
    rw [size_num]
    omega
  · rw [Fin.addCases_right, size_tmCons, size_tmCons, size_c]
    have h1 := size_gN H (.part κ)
    have h3 := size_bodyTm H (Fin.natAdd K κ)
    rw [size_num]
    omega

theorem size_basesTm (p : Fin (K + K)) : (basesTm C p).tree.size ≤ 140 * (X * Lc) := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := H.facts
  have h1 := size_baseTm H p
  have h2 := size_gN H (.dg p)
  rw [basesTm, size_tmCons]
  omega

theorem length_allIds : (G.allIds (K + K) U0 M.N U1).length ≤ X := by
  rw [G.allIds, Finset.length_toList, Finset.card_univ]
  exact H.hId

theorem length_allRoles : (Grp.allRoles M).length ≤ X := by
  refine le_trans (le_of_eq ?_) H.hR
  rw [Grp.allRoles, List.length_flatMap, Fintype.card_sigma]
  have : ∀ x : Fin E, ((univ : Finset (M.kind x).Ro).toList.map (Sigma.mk (β := fun x => (M.kind x).Ro) x)).length = Fintype.card (M.kind x).Ro := by
    intro x
    rw [List.length_map, Finset.length_toList, Finset.card_univ]
  simp only [this]
  rw [← List.ofFn_eq_map, List.sum_ofFn]

variable {d1 : Tree} (hd1 : d1.size ≤ 4 * Lc + 1) {gt : Fin mm → Tree} (hgt : ∀ g, (gt g).size ≤ 4 * Lc + 1)

include hd1

theorem size_slotTm (z : M.Z) (a : Fin (K + K + A')) : (slotTm C tab d1 z a).tree.size ≤ 50 * (X * Lc) := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := H.facts
  rw [slotTm]
  refine (size_catTm_le (n := X) (b := 12 * Lc + 21) (by
    rw [List.length_map, List.length_reverse]; exact length_allIds H) ?_).trans ?_
  · intro t ht
    rw [List.mem_map] at ht
    obtain ⟨id, -, rfl⟩ := ht
    have h1 := size_bits (H.nm (.slp (tab.kcons z id)))
    have h2 := size_bits (H.key (a, id))
    rw [size_ifTm, size_c]
    simp only [listT, Tree.size]
    omega
  · have : X * (12 * Lc + 21 + 11) = 12 * (X * Lc) + 32 * X := by ring
    omega

theorem size_roleTm (r : M.R) : (roleTm C tab tg d1 r).tree.size ≤ 120 * (X * Lc) ^ 2 := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := H.facts
  have h1 := size_listTm_le (ts := (univ : Finset ((M.kind r.1).SlAt r.2)).toList.map fun e =>
    slotTm C tab d1 ⟨r.1, e.1⟩ (M.rp r)) (n := X) (b := 50 * (X * Lc)) (by
      rw [List.length_map, Finset.length_toList, Finset.card_univ]; exact H.Sl r) (by
      intro t ht
      rw [List.mem_map] at ht
      obtain ⟨e, -, rfl⟩ := ht
      exact size_slotTm tab H hd1 _ _)
  have h2 := size_listTm_le (ts := (univ : Finset ((M.kind r.1).CnAt r.2)).toList.map fun ν =>
    gN C (.ch ⟨r.1, ν.1⟩ (decide ((M.kind r.1).c ν.1 ≠ r.2)))) (n := X) (b := 4 * Lc + 5) (by
      rw [List.length_map, Finset.length_toList, Finset.card_univ]; exact H.Cn r) (by
      intro t ht
      rw [List.mem_map] at ht
      obtain ⟨e, -, rfl⟩ := ht
      exact size_gN H _)
  have h3 := size_gN H (.num r.1)
  have h4 := H.htg r
  rw [roleTm, size_tmCons, size_tmCons, size_tmCons, size_c, size_num]
  have e1 : X * (50 * (X * Lc) + 7) = 50 * (X * (X * Lc)) + 7 * X := by ring
  have e2 : X * (4 * Lc + 5 + 7) = 4 * (X * Lc) + 12 * X := by ring
  omega

omit hd1 in
theorem size_oneTm {k : List Bool} (hk : k.length ≤ Lc) (id : G.Uid (K + K) U0 M.N U1) :
    (oneTm C k id).tree.size ≤ 8 * Lc + 50 := by
  have h1 := size_bits hk
  have h2 := size_gN H (.cont id)
  rw [oneTm, size_listTm]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_singleton, size_tmCons, size_c, size_num]
  omega

include hgt

theorem size_endTm (g : Fin mm) (id : G.Uid (K + K) U0 M.N U1) :
    (endTm C tab gt d1 g id).tree.size ≤ 300 * (X * Lc) := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := H.facts
  have h1 := size_bits (H.nm (.slp (tab.kcur id)))
  have h2 := size_bits (H.nm (.slp (tab.kgrp (G.hold0 M.np id))))
  have h3 := size_bits (H.nm (.slp (tab.kgrp (G.hold1 M.np id))))
  have h4 := size_bits (H.key (G.hold0 M.np id, id))
  have h5 := size_bits (H.key (G.hold1 M.np id, id))
  have h6 := size_oneTm H (H.key (G.hold0 M.np id, id)) id
  have h7 := size_oneTm H (H.key (G.hold1 M.np id, id)) id
  have h8 := hgt g
  rw [endTm, size_ifTm, size_ifeq, size_ifeq, size_ifTm, size_c]
  simp only [listT, Grp.Ins.tree, Tree.size, size_num]
  omega

variable {bT bub : List Bool} (hbT : bT.length ≤ Lc) (hbub : bub.length ≤ Lc)

include hbT hbub

theorem size_scriptTm (g : Fin mm) : (scriptTm C tab tg bT bub gt d1 g).tree.size ≤ 720 * (X * Lc) ^ 3 := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := H.facts
  have f6 : (X * Lc) ^ 2 ≤ (X * Lc) ^ 3 := Nat.pow_le_pow_right f4 (by norm_num)
  have f7 : X * (X * Lc) ^ 2 ≤ (X * Lc) ^ 3 := by
    rw [pow_succ (X * Lc) 2, mul_comm]
    exact Nat.mul_le_mul_left _ f1
  have k1 := size_bits hbT
  have k2 := size_bits hbub
  have h1 := sum_le (l := (List.finRange (K + K)).map fun p =>
      ifTm (C.nm (.slp (tab.kgrp (Fin.castAdd A' p)))) (gt g) (basesTm C p)) (f := fun t => t.tree.size) (n := X)
      (b := 170 * (X * Lc)) (by rw [List.length_map, List.length_finRange]; exact H.hK2) (by
        intro t ht
        rw [List.mem_map] at ht
        obtain ⟨p, -, rfl⟩ := ht
        have a1 := size_bits (H.nm (.slp (tab.kgrp (Fin.castAdd A' p))))
        have a2 := size_basesTm H p
        have a3 := hgt g
        rw [size_ifTm]
        omega)
  have h2 := sum_le (l := (Grp.allRoles M).map fun r =>
      ifTm (C.nm (.slp (tab.kgrp (M.rp r)))) (gt g) (listTm [roleTm C tab tg d1 r])) (f := fun t => t.tree.size) (n := X)
      (b := 160 * (X * Lc) ^ 2) (by rw [List.length_map]; exact length_allRoles H) (by
        intro t ht
        rw [List.mem_map] at ht
        obtain ⟨r, -, rfl⟩ := ht
        have a1 := size_bits (H.nm (.slp (tab.kgrp (M.rp r))))
        have a2 := size_roleTm tab H hd1 r
        have a3 := hgt g
        rw [size_ifTm, size_listTm]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_singleton]
        omega)
  have h3 := sum_le (l := (G.allIds (K + K) U0 M.N U1).map (endTm C tab gt d1 g)) (f := fun t => t.tree.size) (n := X)
      (b := 300 * (X * Lc)) (by rw [List.length_map]; exact length_allIds H) (by
        intro t ht
        rw [List.mem_map] at ht
        obtain ⟨id, -, rfl⟩ := ht
        exact size_endTm tab H hd1 hgt g id)
  have l1 : ((List.finRange (K + K)).map fun p =>
      ifTm (C.nm (.slp (tab.kgrp (Fin.castAdd A' p)))) (gt g) (basesTm C p)).length ≤ X := by
    rw [List.length_map, List.length_finRange]; exact H.hK2
  have l2 : ((Grp.allRoles M).map fun r =>
      ifTm (C.nm (.slp (tab.kgrp (M.rp r)))) (gt g) (listTm [roleTm C tab tg d1 r])).length ≤ X := by
    rw [List.length_map]; exact length_allRoles H
  have l3 : ((G.allIds (K + K) U0 M.N U1).map (endTm C tab gt d1 g)).length ≤ X := by
    rw [List.length_map]; exact length_allIds H
  rw [scriptTm, size_tmCons, size_c, size_catTm, List.map_append, List.map_append, List.sum_append, List.sum_append,
    List.length_append, List.length_append]
  simp only [Tree.size]
  have e1 : X * (170 * (X * Lc)) = 170 * (X * (X * Lc)) := by ring
  have e2 : X * (160 * (X * Lc) ^ 2) = 160 * (X * (X * Lc) ^ 2) := by ring
  have e3 : X * (300 * (X * Lc)) = 300 * (X * (X * Lc)) := by ring
  omega

variable {gp : Tree} (hgp : gp.size ≤ X)

include hgp

theorem size_instTm (g : Fin mm) : (instTm C tab tg bT bub gt d1 gp g).tree.size ≤ 740 * (X * Lc) ^ 3 := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := H.facts
  have f6 : (X * Lc) ^ 2 ≤ (X * Lc) ^ 3 := Nat.pow_le_pow_right f4 (by norm_num)
  have h := size_scriptTm tab H hd1 hgt hbT hbub g
  rw [instTm, size_tmCons, size_c]
  omega

variable (hmm : mm ≤ X) {nl nub : List Bool} (hnl : nl.length ≤ Lc) (hnub : nub.length ≤ Lc) (hc : c ≤ X)

include hmm hnl hnub hc

/-- **The size of the dealing program.** -/
theorem size_dealProg : (dealProg C tab qn tg bT bub nl nub gt d1 gp cb b0 b1 i e hU0 hU1).code.size ≤
    (dealC + 3000) * (X * Lc) ^ 4 := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := H.facts
  have f6 : (X * Lc) ^ 2 ≤ (X * Lc) ^ 4 := Nat.pow_le_pow_right f4 (by norm_num)
  have f7 : 1 ≤ (X * Lc) ^ 4 := Nat.one_le_pow _ _ f4
  have k1 := size_bits hnl
  have k2 := size_bits hnub
  have hlT : ∀ b : Γ, (lT cb b).size ≤ 4 * X + 1 := fun b => by
    have := size_ofBits (List.ofFn (cb (some b)))
    rw [List.length_ofFn] at this
    rw [lT]
    omega
  have t0 := hlT b0
  have t1 := hlT b1
  have s1 : (listT ((List.finRange K).map fun κ => ofBits (C.nm (.part κ)))).size ≤ 19 * (X * Lc) :=
    size_keysL H (f := fun κ => C.nm (.part κ)) (by
      rw [List.length_finRange]; have := H.hK1; omega) fun κ => H.nm _
  have s1' : (((List.finRange K).map fun κ => C.nm (.part κ)).map ofBits) =
      (List.finRange K).map fun κ => ofBits (C.nm (.part κ)) := by
    rw [List.map_map]
    rfl
  have s2 := size_listT_le (l := (steps18 C tab qn i e hU0 hU1).map DStep.tree) (n := 11 * X ^ 2)
    (b := 120 * (X * Lc) ^ 2) (by rw [List.length_map]; exact length_steps18 tab i e hU0 hU1 H) (by
      intro t ht
      rw [List.mem_map] at ht
      obtain ⟨st, hst, rfl⟩ := ht
      exact size_steps18 tab i e hU0 hU1 H st hst)
  have s3 := size_listT_le (l := (steps9 C).map DStep.tree) (n := X) (b := 8 * Lc + 9) (by
      rw [List.length_map, steps9, List.length_map, Finset.length_toList, Finset.card_univ]; exact H.hId) (by
      intro t ht
      rw [List.mem_map] at ht
      obtain ⟨st, hst, rfl⟩ := ht
      rw [steps9, List.mem_map] at hst
      obtain ⟨id, -, rfl⟩ := hst
      have a1 := size_bits (H.nm (.cut id))
      have a2 := size_bits (H.nm (.cont id))
      rw [size_dbits]
      omega)
  have s4 := size_listT_le (l := ((List.finRange mm).map (instTm C tab tg bT bub gt d1 gp)).map Tm.tree) (n := X)
    (b := 740 * (X * Lc) ^ 3) (by rw [List.length_map, List.length_map, List.length_finRange]; exact hmm) (by
      intro t ht
      rw [List.mem_map] at ht
      obtain ⟨tm, htm, rfl⟩ := ht
      rw [List.mem_map] at htm
      obtain ⟨g, -, rfl⟩ := htm
      exact size_instTm tab H hd1 hgt hbT hbub hgp g)
  have h := size_dealF (lT cb b0) (lT cb b1) ((List.finRange K).map fun κ => C.nm (.part κ)) nl nub
    (steps18 C tab qn i e hU0 hU1) (steps9 C) ((List.finRange mm).map (instTm C tab tg bT bub gt d1 gp))
  rw [s1'] at h
  rw [dealProg]
  have e1 : 11 * X ^ 2 * (120 * (X * Lc) ^ 2 + 1) ≤ 1331 * (X * Lc) ^ 4 := by
    have a1 : X ^ 2 ≤ (X * Lc) ^ 2 := Nat.pow_le_pow_left f1 2
    have a2 : 1 ≤ (X * Lc) ^ 2 := Nat.one_le_pow _ _ f4
    calc 11 * X ^ 2 * (120 * (X * Lc) ^ 2 + 1) ≤ 11 * (X * Lc) ^ 2 * (121 * (X * Lc) ^ 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ a1) (by omega)
      _ = 1331 * (X * Lc) ^ 4 := by ring
  have e2 : X * (8 * Lc + 9 + 1) = 8 * (X * Lc) + 10 * X := by ring
  have e3 : X * (740 * (X * Lc) ^ 3 + 1) ≤ 741 * (X * Lc) ^ 4 := by
    have a2 : 1 ≤ (X * Lc) ^ 3 := Nat.one_le_pow _ _ f4
    calc X * (740 * (X * Lc) ^ 3 + 1) ≤ (X * Lc) * (741 * (X * Lc) ^ 3) := Nat.mul_le_mul f1 (by omega)
      _ = 741 * (X * Lc) ^ 4 := by ring
  have e4 : dealC ≤ dealC * (X * Lc) ^ 4 := Nat.le_mul_of_pos_right _ f7
  have e5 : (dealC + 3000) * (X * Lc) ^ 4 = dealC * (X * Lc) ^ 4 + 3000 * (X * Lc) ^ 4 := by ring
  omega

end sizes

end Nc.Dl
