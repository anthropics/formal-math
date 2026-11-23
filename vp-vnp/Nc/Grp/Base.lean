/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Grp.Put
import Nc.Grp.Script
import Nc.Grp.RoleProg

/-!
# The program of a base party

The automaton is simulated (or the part of the input is taken); the letters of every tape are cut into segments for the
partners; the strings of the partners are cut into units.
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree Finset

variable {A : Type} [CommRing A] {θ : List Bool → A}

section seg

/-- Items: flags and letters of a tape. -/
abbrev Item := List ℕ × List (List Bool)

/-- As a tree. -/
def encI (it : Item) : Tree := .cons (listT (it.1.map num)) (listT (it.2.map ofBits))

/-- Strings as a tree. -/
def encA (l : List (List Bool)) : Tree := listT (l.map ofBits)

variable (A) in
/-- One tape. -/
def segOne (sep : List Bool) (it : Item) (accs : List (List Bool)) : List (A × List (List Bool)) :=
  (segRow sep it.1 accs it.2).map fun out => ((1 : A), out.reverse)

theorem length_segL (sep : List Bool) (m f : ℕ) (tk : Bool) (cur : List Bool) (fs : List ℕ) (as rest out : List (List Bool))
    (hm : fs.length + rest.length ≤ m) :
    ∀ l ∈ segL sep f tk cur fs as rest out, l.length = fs.length + 1 + out.length := by
  induction m generalizing f tk cur fs as rest out with
  | zero =>
    intro l hl
    have h1 : fs = [] := List.length_eq_zero_iff.1 (by omega)
    have h2 : rest = [] := List.length_eq_zero_iff.1 (by omega)
    subst h1 h2
    rw [segL_eq] at hl
    simp only [closeL, takeL, List.append_nil, if_true] at hl
    split_ifs at hl
    · rw [List.mem_singleton] at hl
      subst hl
      simp
      omega
    · simp at hl
  | succ m ih =>
    intro l hl
    rw [segL_eq, List.mem_append] at hl
    rcases hl with hl | hl
    · split_ifs at hl
      · unfold closeL at hl
        cases fs with
        | nil =>
          simp only at hl
          split_ifs at hl
          · rw [List.mem_singleton] at hl
            subst hl
            simp
            omega
          · simp at hl
        | cons f' fs' =>
          have := ih f' false _ fs' as.tail rest (cur :: out) (by simp only [List.length_cons] at hm; omega) l hl
          simp only [List.length_cons] at this ⊢
          omega
      · simp at hl
    · unfold takeL at hl
      cases rest with
      | nil => simp at hl
      | cons a r => exact ih f true _ fs as r out (by simp only [List.length_cons] at hm; omega) l hl

theorem length_segRow {sep : List Bool} {fl : List ℕ} {accs l : List (List Bool)} :
    ∀ out ∈ segRow sep fl accs l, out.length = fl.length := by
  intro out hout
  cases fl with
  | nil => simp [segRow] at hout
  | cons f fs =>
    have := length_segL sep _ f false _ fs accs.tail l [] le_rfl out hout
    simpa using this

/-- Step: argument ((flags, letters), strings). -/
def segStepF (sep : List Bool) : Fm := .ite (.hd (.hd .id))
  (lett (app (segB sep).code (.cons (.quote (segB sep).code) (.cons (.hd (.hd (.hd .id))) (.cons (.quote .nil)
    (.cons (appF (.quote (ofBits sep)) (.hd (.tl .id))) (.cons (.tl (.hd (.hd .id))) (.cons (.tl (.tl .id))
      (.cons (.tl (.hd .id)) (.quote .nil))))))))) (foldF .id (.quote .nil) .id)) .fail

theorem segStepF_does (sep : List Bool) (c : ℕ) (hsep : sep.length ≤ c) (it : Item) (accs : List (List Bool))
    (hc : ∀ a ∈ it.2, a.length ≤ c) : Does θ (segStepF sep) (.cons (encI it) (encA accs))
      ((segOne A sep it accs).map (Prod.map id encA)) ((62 * c + 700) * (it.1.length + it.2.length + 1)) := by
  obtain ⟨fl, l⟩ := it
  set x : Tree := .cons (encI (fl, l)) (encA accs) with hx
  cases fl with
  | nil =>
    refine ((Does.ite_false (Gives.id _).hd.hd (Does.fail _)).replace ?_).mono ?_
    · simp [segOne, segRow]
    · simp only [List.length_nil]
      nlinarith
  | cons f fs =>
    have e1 : Gives θ (appF (.quote (ofBits sep)) (.hd (.tl .id))) x (ofBits (sep ++ accs.headD []))
        (1 + 3 + sep.length * 62 + 41) := by
      refine appB_gives (Gives.quote _ _) ?_
      rw [← listB_hd]
      exact (Gives.id _).tl.hd
    have e2 : Gives θ (.tl (.tl .id)) x (listT (accs.tail.map ofBits)) 3 := by
      rw [← listB_tl]
      exact (Gives.id _).tl.tl
    have e3 : Gives θ (.cons (.quote (segB sep).code) (.cons (.hd (.hd (.hd .id))) (.cons (.quote .nil)
        (.cons (appF (.quote (ofBits sep)) (.hd (.tl .id))) (.cons (.tl (.hd (.hd .id))) (.cons (.tl (.tl .id))
        (.cons (.tl (.hd .id)) (.quote .nil)))))))) x
        (.cons (segB sep).code (segS f false (sep ++ accs.headD []) fs accs.tail l [])) (62 * c + 100) :=
      (Gives.cons (Gives.quote _ _) (Gives.cons (Gives.id _).hd.hd.hd (Gives.cons (Gives.quote _ _) (Gives.cons e1
        (Gives.cons (Gives.id _).hd.hd.tl (Gives.cons e2 (Gives.cons (Gives.id _).hd.tl (Gives.quote _ _)))))))).mono
        (by omega)
    have e4 := segB_does (θ := θ) sep c hsep (fs.length + l.length) f false (sep ++ accs.headD []) fs accs.tail l [] le_rfl hc
    have e5 := Does.appT (p := (segB sep).code) (l := [((1 : A), ())])
      (enc := fun _ => .cons (segB sep).code (segS f false (sep ++ accs.headD []) fs accs.tail l []))
      (f := fun _ => encL (segL sep f false (sep ++ accs.headD []) fs accs.tail l [])) e3 (fun b _ => by
        rw [Fm.ofTree_code]
        exact e4)
    rw [bindL_single] at e5
    have e6 : Does θ (app (segB sep).code (.cons (.quote (segB sep).code) (.cons (.hd (.hd (.hd .id))) (.cons (.quote .nil)
        (.cons (appF (.quote (ofBits sep)) (.hd (.tl .id))) (.cons (.tl (.hd (.hd .id))) (.cons (.tl (.tl .id))
        (.cons (.tl (.hd .id)) (.quote .nil))))))))) x
        (((segRow sep (f :: fs) accs l).map fun out => ((1 : A), out)).map (Prod.map id encA)) _ := e5.replace (by
      rw [List.map_map]
      rfl)
    have e7 := Does.lettE (G := foldF .id (.quote .nil) .id) (f := fun out => [((1 : A), out.reverse)]) (enc' := encA)
      (d := (fs.length + 1) * 31 + 30) e6 (fun b hb => by
        obtain ⟨out, hout, rfl⟩ := List.mem_map.1 hb
        have h1 := length_segRow out hout
        have := rev_gives (θ := θ) (x := encA out) (ys := []) (xs := out.map ofBits) (s := .quote .nil) (l := .id)
          (Gives.quote _ _) (Gives.id _)
        rw [List.append_nil, ← List.map_reverse, List.length_map, h1, List.length_cons] at this
        exact this.mono (by omega))
    have hne : x.hd.hd ≠ .nil := by simp [hx, encI, listT]
    refine ((Does.ite_true (Gives.id x).hd.hd hne e7).replace ?_).mono ?_
    · congr 1
      rw [bindL_pure _ (fun out => out)]
      simp [segOne, flatMap_single]
    · simp only [List.length_cons]
      nlinarith

variable (A) in
/-- Several tapes (the last one first). -/
def segsL (sep : List Bool) (items : List Item) (accs : List (List Bool)) : List (A × List (List Bool)) :=
  foldL (segOne A sep) items accs

/-- Several tapes: argument (items, strings). -/
def segsF (sep : List Bool) : Fm := foldF (segStepF sep) (.tl .id) (.hd .id)

theorem segsF_does (sep : List Bool) (c : ℕ) (hsep : sep.length ≤ c) (items : List Item) (accs : List (List Bool))
    (hc : ∀ it ∈ items, ∀ a ∈ it.2, a.length ≤ c) : Does θ (segsF sep) (.cons (listT (items.map encI)) (encA accs))
      ((segsL A sep items accs).map (Prod.map id encA))
      ((items.map fun it => (62 * c + 700) * (it.1.length + it.2.length + 1) + 30).sum + 30) := by
  have := foldT (θ := θ) (A := A) (encE := encI) (xs := items) (enc := encA) (s₀ := accs) (f := segOne A sep)
    (Inv := fun _ _ => True) (d := fun it => (62 * c + 700) * (it.1.length + it.2.length + 1)) (step := segStepF sep)
    (s := .tl .id) (l := .hd .id) (x := .cons (listT (items.map encI)) (encA accs)) (Gives.id _).tl (Gives.id _).hd
    (fun it _ accs hit _ => ⟨segStepF_does sep c hsep it accs (hc it hit), fun _ _ => trivial⟩) trivial
  exact this.mono (by omega)

end seg

end Nc.Grp
