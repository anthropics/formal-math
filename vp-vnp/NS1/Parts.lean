/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.Picks

/-!
# Parts of a list, written into a trie
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

/-- A step: the argument is (path, (trie, (number, rest))); take elements from the rest and write them, in reversed
order, at the path. -/
def partStep : Fm := lett
  (.cons (app takeB.code (.cons (.quote takeB.code) (.cons (.hd (.tl (.tl .id))) (.cons (.quote .nil) (.tl (.tl (.tl .id)))))))
    .id)
  (.cons (setF (.hd (.tl .id)) (.hd (.hd .id)) (.hd (.tl (.tl .id)))) (.cons (.hd (.tl (.tl (.tl .id)))) (.tl (.hd .id))))

/-- The function of a step. -/
def partFun (m : ℕ) (x σ : Tree) : Tree :=
  .cons (tset x.path (listT (σ.tl.tl.toList.take m).reverse) σ.hd) (.cons σ.tl.hd (listT (σ.tl.tl.toList.drop m)))

theorem partStep_gives (x W : Tree) (w : List Bool) (l : List Tree) :
    Gives θ partStep (.cons x (.cons W (.cons (ofBits w) (listT l)))) (partFun (KT.val w) x (.cons W (.cons (ofBits w) (listT l))))
      (((l.take (KT.val w)).length + 1) * (60 * w.length + 100) + 60 * x.len + 100) := by
  have h1 := Gives.app (p := takeB.code) (Gives.cons (Gives.quote (θ := θ) takeB.code
    (.cons x (.cons W (.cons (ofBits w) (listT l))))) (Gives.cons (Gives.id _).tl.tl.hd
      (Gives.cons (Gives.quote (listT []) _) (Gives.id _).tl.tl.tl))) (by rw [Fm.ofTree_code]; exact takeB_gives w [] l)
  have h2 := Gives.cons h1 (Gives.id (θ := θ) (.cons x (.cons W (.cons (ofBits w) (listT l)))))
  rw [List.append_nil] at h2
  have h3 := setF_gives (Gives.id (θ := θ) (.cons (.cons (listT (l.take (KT.val w)).reverse) (listT (l.drop (KT.val w))))
    (.cons x (.cons W (.cons (ofBits w) (listT l)))))).tl.hd (Gives.id _).hd.hd (Gives.id _).tl.tl.hd
  have h4 := Gives.lett h2 (Gives.cons h3 (Gives.cons (Gives.id _).tl.tl.tl.hd (Gives.id _).hd.tl))
  have e : partFun (KT.val w) x (.cons W (.cons (ofBits w) (listT l))) =
      .cons (tset x.path (listT (l.take (KT.val w)).reverse) W) (.cons (ofBits w) (listT (l.drop (KT.val w)))) := by
    simp [partFun]
  rw [e]
  refine Gives.mono h4 ?_
  simp only [tl_cons, hd_cons]
  omega

/-- Write the parts of a list: `names` are the paths, `n` the length of the parts in binary, `l` gives the list. -/
def partsF (names : List (List Bool)) (n : List Bool) (l : Fm) : Fm :=
  .hd (foldF partStep (.cons (.quote .nil) (.cons (.quote (ofBits n)) l)) (.quote (listT (names.map ofBits))))

/-- The trie with the parts. -/
def partsT (m : ℕ) : List (List Bool) → Tree → List Tree → Tree
  | [], W, _ => W
  | p :: ps, W, l => partsT m ps (tset p (listT (l.take m).reverse) W) (l.drop m)

theorem foldl_partFun (m : ℕ) (names : List (List Bool)) (W nT : Tree) (l : List Tree) :
    ((names.map ofBits).foldl (fun σ x => partFun m x σ) (.cons W (.cons nT (listT l)))).hd = partsT m names W l := by
  induction names generalizing W l with
  | nil => rfl
  | cons p ps ih =>
    rw [List.map_cons, List.foldl_cons, partsT]
    simp only [partFun, hd_cons, tl_cons, toList_listT, path_ofBits]
    exact ih _ _

theorem partsF_gives {lf : Fm} {x : Tree} {cl : ℕ} {l : List Tree} (hl : Gives θ lf x (listT l) cl)
    (names : List (List Bool)) (n : List Bool) (Ln : ℕ) (hn : ∀ p ∈ names, p.length ≤ Ln) :
    Gives θ (partsF names n lf) x (partsT (KT.val n) names .nil l)
      (cl + (l.length + names.length) * (60 * n.length + 100) + names.length * (60 * Ln + 130) + 40) := by
  -- the cost of the steps depends on the rest; we count with a potential
  have key : ∀ (ps : List (List Bool)) (W : Tree) (l : List Tree), (∀ p ∈ ps, p.length ≤ Ln) →
      Gives θ (foldB partStep) (.cons (foldB partStep).code (.cons (.cons W (.cons (ofBits n) (listT l)))
        (listT (ps.map ofBits)))) ((ps.map ofBits).foldl (fun σ x => partFun (KT.val n) x σ)
        (.cons W (.cons (ofBits n) (listT l)))) ((l.length + ps.length) * (60 * n.length + 100) + ps.length * (60 * Ln + 130) + 10) := by
    intro ps
    induction ps with
    | nil =>
      intro W l _
      exact (Gives.ite_false (Gives.id _).tl.tl (Gives.id _).tl.hd).mono (by omega)
    | cons p ps ih =>
      intro W l hps
      have hstep := partStep_gives (θ := θ) (ofBits p) W n l
      have e : partFun (KT.val n) (ofBits p) (.cons W (.cons (ofBits n) (listT l))) =
          .cons (tset p (listT (l.take (KT.val n)).reverse) W) (.cons (ofBits n) (listT (l.drop (KT.val n)))) := by
        simp [partFun]
      have e1 : Gives θ (lett (.cons (.hd (.tl (.tl .id))) (.hd (.tl .id))) partStep)
          (.cons (foldB partStep).code (.cons (.cons W (.cons (ofBits n) (listT l))) (listT ((p :: ps).map ofBits))))
          (partFun (KT.val n) (ofBits p) (.cons W (.cons (ofBits n) (listT l)))) _ :=
        Gives.lett (Gives.cons (Gives.id _).tl.tl.hd (Gives.id _).tl.hd) hstep
      have ih' : Gives θ (Fm.ofTree (foldB partStep).code) (.cons (foldB partStep).code
          (.cons (.cons (tset p (listT (l.take (KT.val n)).reverse) W) (.cons (ofBits n) (listT (l.drop (KT.val n)))))
          (listT (ps.map ofBits)))) ((ps.map ofBits).foldl (fun σ x => partFun (KT.val n) x σ)
          (.cons (tset p (listT (l.take (KT.val n)).reverse) W) (.cons (ofBits n) (listT (l.drop (KT.val n))))))
          (((l.drop (KT.val n)).length + ps.length) * (60 * n.length + 100) + ps.length * (60 * Ln + 130) + 10) := by
        rw [Fm.ofTree_code]
        exact ih _ _ fun q hq => hps q (List.mem_cons_of_mem _ hq)
      rw [e] at e1
      have r := Gives.run (Gives.id (θ := θ) (.cons (foldB partStep).code (.cons (.cons W (.cons (ofBits n) (listT l)))
        (listT ((p :: ps).map ofBits))))).hd (Gives.cons (Gives.id _).hd (Gives.cons e1 (Gives.id _).tl.tl.tl)) ih'
      rw [List.map_cons, List.foldl_cons, e]
      refine (Gives.ite_true (Gives.id _).tl.tl (by simp [listT]) r).mono ?_
      have hp := hps p List.mem_cons_self
      have hlen : (l.take (KT.val n)).length + (l.drop (KT.val n)).length = l.length := by
        rw [← List.length_append, List.take_append_drop]
      simp only [List.length_cons, len_ofBits]
      have e3 : (l.length + (ps.length + 1)) * (60 * n.length + 100) = ((l.take (KT.val n)).length + 1) * (60 * n.length + 100) +
          ((l.drop (KT.val n)).length + ps.length) * (60 * n.length + 100) := by
        rw [← hlen]
        ring
      have e4 : (ps.length + 1) * (60 * Ln + 130) = ps.length * (60 * Ln + 130) + (60 * Ln + 130) := by ring
      omega
  have h0 := Gives.cons (Gives.quote (θ := θ) .nil x) (Gives.cons (Gives.quote (ofBits n) x) hl)
  have h1 := Gives.app (p := (foldB partStep).code) (Gives.cons (Gives.quote (θ := θ) (foldB partStep).code x)
    (Gives.cons h0 (Gives.quote (listT (names.map ofBits)) x))) (by rw [Fm.ofTree_code]; exact key names .nil l hn)
  have h2 := Gives.hd h1
  rw [foldl_partFun] at h2
  exact h2.mono (by omega)

end NS1
