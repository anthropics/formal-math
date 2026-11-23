/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Grp.Trans

/-!
# Cutting the letters of a tape into segments

The letters come in reverse order; the segments are made from the last partner to the first one. Every segment is
closed by a separator and stands in front of the string that the partner has from the later tapes.
-/

set_option linter.unusedSectionVars false

namespace Nc.Grp

open NS1 NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

/-- Flags: 0 = nothing is taken, 1 = something, 2 = anything. -/
def okFlag (f : ℕ) (tk : Bool) : Bool :=
  match f with
  | 0 => !tk
  | 1 => tk
  | _ => true

/-- All ways to cut the letters `rest`: `f`, `tk`, `cur` flag, `something has been taken`, string of the partner at hand;
`fs`, `as` flags and strings of the partners before; `out` strings of the partners behind. -/
def segL (sep : List Bool) (f : ℕ) (tk : Bool) (cur : List Bool) (fs : List ℕ) (as : List (List Bool))
    (rest : List (List Bool)) (out : List (List Bool)) : List (List (List Bool)) :=
  (if okFlag f tk then
    match fs with
    | [] => if rest = [] then [cur :: out] else []
    | f' :: fs' => segL sep f' false (sep ++ as.headD []) fs' as.tail rest (cur :: out)
  else []) ++
  match rest with
  | [] => []
  | a :: r => segL sep f true (a ++ cur) fs as r out
termination_by fs.length + rest.length

/-- The state of the program. -/
def segS (f : ℕ) (tk : Bool) (cur : List Bool) (fs : List ℕ) (as rest out : List (List Bool)) : Tree :=
  .cons (num f) (.cons (bit tk) (.cons (ofBits cur) (.cons (listT (fs.map num)) (.cons (listT (as.map ofBits))
    (.cons (listT (rest.map ofBits)) (listT (out.map ofBits)))))))

/-- Parts of the state, in the argument (this program, state). -/
def sgF : Fm := .hd (.tl .id)
/-- tk -/
def sgTk : Fm := .hd (.tl (.tl .id))
/-- cur -/
def sgCur : Fm := .hd (.tl (.tl (.tl .id)))
/-- fs -/
def sgFs : Fm := .hd (.tl (.tl (.tl (.tl .id))))
/-- as -/
def sgAs : Fm := .hd (.tl (.tl (.tl (.tl (.tl .id)))))
/-- rest -/
def sgRest : Fm := .hd (.tl (.tl (.tl (.tl (.tl (.tl .id))))))
/-- out -/
def sgOut : Fm := .tl (.tl (.tl (.tl (.tl (.tl (.tl .id))))))

/-- Concatenation of lists of bits. -/
theorem appB_gives {a b : Fm} {x : Tree} {ca cb : ℕ} {v w : List Bool} (ha : Gives θ a x (ofBits v) ca)
    (hb : Gives θ b x (ofBits w) cb) : Gives θ (appF a b) x (ofBits (v ++ w)) (ca + cb + v.length * 62 + 41) := by
  rw [← listT_ofBits] at ha hb ⊢
  have := appF_gives ha hb
  rw [← List.map_append, List.length_map] at this
  exact this

/-- The next partner. -/
def segNext (sep : List Bool) : Fm := .cons (.hd .id) (.cons (.hd sgFs) (.cons (.quote .nil)
  (.cons (appF (.quote (ofBits sep)) (.hd sgAs)) (.cons (.tl sgFs) (.cons (.tl sgAs) (.cons sgRest
  (.cons sgCur sgOut)))))))

/-- Take a letter. -/
def segTake : Fm := .cons (.hd .id) (.cons sgF (.cons (.quote one) (.cons (appF (.hd sgRest) sgCur)
  (.cons sgFs (.cons sgAs (.cons (.tl sgRest) sgOut))))))

/-- Close a segment. -/
def segClose (sep : List Bool) : Fm := .ite sgFs (.run (.hd .id) (segNext sep)) (.ite sgRest .fail (.cons sgCur sgOut))

/-- The program. -/
def segB (sep : List Bool) : Fm := .ite .guess
  (.ite sgF (.ite (.tl sgF) (segClose sep) (.ite sgTk (segClose sep) .fail)) (.ite sgTk .fail (segClose sep)))
  (.ite sgRest (.run (.hd .id) segTake) .fail)

section parts

variable {p : Tree} {f : ℕ} {tk : Bool} {cur : List Bool} {fs : List ℕ} {as rest out : List (List Bool)}

theorem sgF_gives : Gives θ sgF (.cons p (segS f tk cur fs as rest out)) (num f) 3 := (Gives.id _).tl.hd

theorem sgTk_gives : Gives θ sgTk (.cons p (segS f tk cur fs as rest out)) (bit tk) 4 := (Gives.id _).tl.tl.hd

theorem sgCur_gives : Gives θ sgCur (.cons p (segS f tk cur fs as rest out)) (ofBits cur) 5 :=
  (Gives.id _).tl.tl.tl.hd

theorem sgFs_gives : Gives θ sgFs (.cons p (segS f tk cur fs as rest out)) (listT (fs.map num)) 6 :=
  (Gives.id _).tl.tl.tl.tl.hd

theorem sgAs_gives : Gives θ sgAs (.cons p (segS f tk cur fs as rest out)) (listT (as.map ofBits)) 7 :=
  (Gives.id _).tl.tl.tl.tl.tl.hd

theorem sgRest_gives : Gives θ sgRest (.cons p (segS f tk cur fs as rest out)) (listT (rest.map ofBits)) 8 :=
  (Gives.id _).tl.tl.tl.tl.tl.tl.hd

theorem sgOut_gives : Gives θ sgOut (.cons p (segS f tk cur fs as rest out)) (listT (out.map ofBits)) 8 :=
  (Gives.id _).tl.tl.tl.tl.tl.tl.tl

end parts

theorem listB_hd (l : List (List Bool)) : (listT (l.map ofBits)).hd = ofBits (l.headD []) := by cases l <;> rfl

theorem listB_tl (l : List (List Bool)) : (listT (l.map ofBits)).tl = listT (l.tail.map ofBits) := by cases l <;> rfl

/-- The results of a program without weights. -/
abbrev encL (l : List (List (List Bool))) : List (A × Tree) := l.map fun l => ((1 : A), listT (l.map ofBits))

/-- What remains to do when a segment is closed. -/
def closeL (sep cur : List Bool) (fs : List ℕ) (as rest out : List (List Bool)) : List (List (List Bool)) :=
  match fs with
  | [] => if rest = [] then [cur :: out] else []
  | f' :: fs' => segL sep f' false (sep ++ as.headD []) fs' as.tail rest (cur :: out)

/-- What remains to do when a letter is taken. -/
def takeL (sep : List Bool) (f : ℕ) (cur : List Bool) (fs : List ℕ) (as rest out : List (List Bool)) :
    List (List (List Bool)) :=
  match rest with
  | [] => []
  | a :: r => segL sep f true (a ++ cur) fs as r out

theorem segL_eq (sep : List Bool) (f : ℕ) (tk : Bool) (cur : List Bool) (fs : List ℕ) (as rest out : List (List Bool)) :
    segL sep f tk cur fs as rest out =
      (if okFlag f tk then closeL sep cur fs as rest out else []) ++ takeL sep f cur fs as rest out := by
  rw [segL.eq_def]
  cases fs <;> cases rest <;> rfl

section step

variable {sep : List Bool} {c d f : ℕ} {tk : Bool} {cur : List Bool} {fs : List ℕ} {as rest out : List (List Bool)}

theorem segClose_does (hsep : sep.length ≤ c) (h1 : ∀ f' fs', fs = f' :: fs' → Does θ (segB sep)
      (.cons (segB sep).code (segS f' false (sep ++ as.headD []) fs' as.tail rest (cur :: out)))
      (encL (segL sep f' false (sep ++ as.headD []) fs' as.tail rest (cur :: out))) d) :
    Does θ (segClose sep) (.cons (segB sep).code (segS f tk cur fs as rest out))
      (encL (closeL sep cur fs as rest out)) (d + 62 * c + 200) := by
  cases fs with
  | nil =>
    cases rest with
    | nil =>
      have e : Gives θ (.cons sgCur sgOut) (.cons (segB sep).code (segS f tk cur [] as [] out))
          (listT ((cur :: out).map ofBits)) 20 := (Gives.cons sgCur_gives sgOut_gives).mono (by omega)
      exact (Does.ite_false sgFs_gives (Does.ite_false sgRest_gives e)).mono (by omega)
    | cons a r =>
      have hne : listT ((a :: r).map ofBits) ≠ .nil := by simp [listT]
      exact (Does.ite_false sgFs_gives (Does.ite_true sgRest_gives hne
        (Does.fail (.cons (segB sep).code (segS f tk cur [] as (a :: r) out))))).mono (by omega)
  | cons f' fs' =>
    have e1 : Gives θ (appF (.quote (ofBits sep)) (.hd sgAs)) (.cons (segB sep).code (segS f tk cur (f' :: fs') as rest out))
        (ofBits (sep ++ as.headD [])) (1 + 8 + sep.length * 62 + 41) := by
      refine appB_gives (Gives.quote _ _) ?_
      rw [← listB_hd]
      exact sgAs_gives.hd
    have e2 : Gives θ (segNext sep) (.cons (segB sep).code (segS f tk cur (f' :: fs') as rest out))
        (.cons (segB sep).code (segS f' false (sep ++ as.headD []) fs' as.tail rest (cur :: out)))
        (62 * c + 150) := by
      have eA : Gives θ (.tl sgAs) (.cons (segB sep).code (segS f tk cur (f' :: fs') as rest out))
          (listT (as.tail.map ofBits)) 8 := by
        rw [← listB_tl]
        exact sgAs_gives.tl
      exact (Gives.cons (Gives.id _).hd (Gives.cons sgFs_gives.hd (Gives.cons (Gives.quote _ _) (Gives.cons e1
        (Gives.cons sgFs_gives.tl (Gives.cons eA (Gives.cons sgRest_gives
          (Gives.cons sgCur_gives sgOut_gives)))))))).mono (by omega)
    have e3 := Does.run (Gives.id (θ := θ) (.cons (segB sep).code (segS f tk cur (f' :: fs') as rest out))).hd e2
      (show Does θ (Fm.ofTree (segB sep).code) _ _ _ by rw [Fm.ofTree_code]; exact h1 f' fs' rfl)
    have hne : listT ((f' :: fs').map num) ≠ .nil := by simp [listT]
    exact (Does.ite_true sgFs_gives hne e3).mono (by omega)

theorem segTake_does (hc : ∀ a ∈ rest, a.length ≤ c) (h2 : ∀ a r, rest = a :: r → Does θ (segB sep)
      (.cons (segB sep).code (segS f true (a ++ cur) fs as r out)) (encL (segL sep f true (a ++ cur) fs as r out)) d) :
    Does θ (.ite sgRest (.run (.hd .id) segTake) .fail) (.cons (segB sep).code (segS f tk cur fs as rest out))
      (encL (takeL sep f cur fs as rest out)) (d + 62 * c + 200) := by
  cases rest with
  | nil =>
    exact (Does.ite_false sgRest_gives (Does.fail (.cons (segB sep).code (segS f tk cur fs as [] out)))).mono (by omega)
  | cons a r =>
    have ha := hc a List.mem_cons_self
    have e1 : Gives θ (appF (.hd sgRest) sgCur) (.cons (segB sep).code (segS f tk cur fs as (a :: r) out))
        (ofBits (a ++ cur)) (9 + 5 + a.length * 62 + 41) := appB_gives sgRest_gives.hd sgCur_gives
    have e2 : Gives θ segTake (.cons (segB sep).code (segS f tk cur fs as (a :: r) out))
        (.cons (segB sep).code (segS f true (a ++ cur) fs as r out)) (62 * c + 150) := by
      refine (Gives.cons (Gives.id _).hd (Gives.cons sgF_gives (Gives.cons (Gives.quote _ _) (Gives.cons e1
        (Gives.cons sgFs_gives (Gives.cons sgAs_gives (Gives.cons sgRest_gives.tl sgOut_gives))))))).mono ?_
      omega
    have e3 := Does.run (Gives.id (θ := θ) (.cons (segB sep).code (segS f tk cur fs as (a :: r) out))).hd e2
      (show Does θ (Fm.ofTree (segB sep).code) _ _ _ by rw [Fm.ofTree_code]; exact h2 a r rfl)
    have hne : listT ((a :: r).map ofBits) ≠ .nil := by simp [listT]
    exact (Does.ite_true sgRest_gives hne e3).mono (by omega)

theorem seg_step (hsep : sep.length ≤ c) (hc : ∀ a ∈ rest, a.length ≤ c)
    (h1 : ∀ f' fs', fs = f' :: fs' → Does θ (segB sep)
      (.cons (segB sep).code (segS f' false (sep ++ as.headD []) fs' as.tail rest (cur :: out)))
      (encL (segL sep f' false (sep ++ as.headD []) fs' as.tail rest (cur :: out))) d)
    (h2 : ∀ a r, rest = a :: r → Does θ (segB sep)
      (.cons (segB sep).code (segS f true (a ++ cur) fs as r out)) (encL (segL sep f true (a ++ cur) fs as r out)) d) :
    Does θ (segB sep) (.cons (segB sep).code (segS f tk cur fs as rest out))
      (encL (segL sep f tk cur fs as rest out)) (d + (62 * c + 300)) := by
  have hcl := segClose_does (f := f) (tk := tk) hsep h1
  have htk := segTake_does (tk := tk) hc h2
  have hok : Does θ (.ite sgF (.ite (.tl sgF) (segClose sep) (.ite sgTk (segClose sep) .fail))
      (.ite sgTk .fail (segClose sep))) (.cons (segB sep).code (segS f tk cur fs as rest out))
      (encL (if okFlag f tk then closeL sep cur fs as rest out else [])) (d + 62 * c + 200 + 30) := by
    have hfail : Does θ .fail (.cons (segB sep).code (segS f tk cur fs as rest out)) (encL (A := A) []) 0 := Does.fail _
    match f, tk with
    | 0, false => exact (Does.ite_false sgF_gives (Does.ite_false sgTk_gives hcl)).mono (by omega)
    | 0, true => exact (Does.ite_false sgF_gives (Does.ite_true sgTk_gives (by simp [bit, one]) hfail)).mono (by omega)
    | 1, false => exact (Does.ite_true sgF_gives (by simp [num]) (Does.ite_false sgF_gives.tl
        (Does.ite_false sgTk_gives hfail))).mono (by omega)
    | 1, true => exact (Does.ite_true sgF_gives (by simp [num]) (Does.ite_false sgF_gives.tl
        (Does.ite_true sgTk_gives (by simp [bit, one]) hcl))).mono (by omega)
    | f + 2, tk =>
      have h2 : num (f + 2) ≠ .nil := by simp [num]
      have h3 : (num (f + 2)).tl ≠ .nil := by simp [num]
      rw [if_pos (show okFlag (f + 2) tk = true from rfl)]
      exact (Does.ite_true (H := .ite sgTk .fail (segClose sep)) sgF_gives h2 (Does.ite_true
        (H := .ite sgTk (segClose sep) .fail) sgF_gives.tl h3 hcl)).mono (by omega)
  refine ((Does.either hok htk).replace ?_).mono (by omega)
  rw [segL_eq]
  simp

end step

/-- **The program cuts.** -/
theorem segB_does (sep : List Bool) (c : ℕ) (hsep : sep.length ≤ c) (m : ℕ) (f : ℕ) (tk : Bool) (cur : List Bool)
    (fs : List ℕ) (as rest out : List (List Bool)) (hm : fs.length + rest.length ≤ m) (hc : ∀ a ∈ rest, a.length ≤ c) :
    Does θ (segB sep) (.cons (segB sep).code (segS f tk cur fs as rest out))
      (encL (segL sep f tk cur fs as rest out)) ((62 * c + 300) * (m + 1)) := by
  induction m generalizing f tk cur fs as rest out with
  | zero =>
    refine (seg_step (d := 0) hsep hc (fun f' fs' h => ?_) fun a r h => ?_).mono (by omega)
    · subst h
      simp at hm
    · subst h
      simp at hm
  | succ m ih =>
    refine (seg_step (d := (62 * c + 300) * (m + 1)) hsep hc (fun f' fs' h => ?_) fun a r h => ?_).mono
      (le_of_eq (by ring))
    · subst h
      exact ih f' false _ fs' as.tail rest (cur :: out) (by simp only [List.length_cons] at hm; omega) hc
    · subst h
      exact ih f true _ fs as r out (by simp only [List.length_cons] at hm; omega) fun b hb =>
        hc b (List.mem_cons_of_mem _ hb)

/-- All ways to cut the letters of a tape. -/
def segRow (sep : List Bool) (fl : List ℕ) (accs l : List (List Bool)) : List (List (List Bool)) :=
  match fl with
  | [] => []
  | f :: fs => segL sep f false (sep ++ accs.headD []) fs accs.tail l []

end Nc.Grp
