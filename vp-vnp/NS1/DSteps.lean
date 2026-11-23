/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import NS1.Deal

/-!
# The interpreter of steps and templates
-/

set_option linter.unusedSectionVars false

namespace NS1

open _root_.NS1.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A}

/-- The values of a trie. -/
def gets (W : Tree) : List Bool → Tree := fun p => tget p W

theorem gets_nil : gets .nil = fun _ => .nil := funext tget_nil

theorem gets_tset (W : Tree) (p : List Bool) (v : Tree) : gets (tset p v W) = Function.update (gets W) p v :=
  funext ((show RepW W (gets W) from fun _ => rfl).set p v)

theorem gets_assign (W o : Tree) : gets (assignT W o) = assignS (gets W) o :=
  funext ((show RepW W (gets W) from fun _ => rfl).assign o)

/-- Steps. -/
inductive DStep where
  /-- choose an option (a list of assignments) from the list that the table has at the value of `p` -/
  | pick (p : List Bool) (tab : Tree)
  /-- `dst := φ (value of p, value of q)` -/
  | op (p q dst : List Bool) (φ : Tree)
  /-- if the value of `p` is not empty: guess a bit list for `dst` -/
  | bits (p dst : List Bool)
  /-- reject if the value of `p` is empty -/
  | check (p : List Bool)

namespace DStep

/-- As a tree. -/
def tree : DStep → Tree
  | pick p tab => .cons (num 0) (.cons (ofBits p) tab)
  | op p q dst φ => .cons (num 1) (.cons (ofBits p) (.cons (ofBits q) (.cons (ofBits dst) φ)))
  | bits p dst => .cons (num 2) (.cons (ofBits p) (ofBits dst))
  | check p => .cons (num 3) (ofBits p)

/-- The states after the step; `m` is the length of guessed bit lists. -/
def exec (m : ℕ) : DStep → (List Bool → Tree) → List (List Bool → Tree)
  | pick p tab, σ => (tget (σ p).path tab).toList.map fun o => assignS σ o
  | op p q dst φ, σ => [Function.update σ dst (tget (σ q).path (tget (σ p).path φ))]
  | bits p dst, σ => if σ p = .nil then [σ] else (allBits m).map fun u => Function.update σ dst (ofBits u.reverse)
  | check p, σ => if σ p = .nil then [] else [σ]

/-- A bound for the cost. `mb`: the number of digits of `m`. -/
def cost (m mb : ℕ) : DStep → (List Bool → Tree) → ℕ
  | pick p tab, σ => 30 * p.length + 30 * (σ p).len + 20 * (tget (σ p).path tab).toList.length +
      ((tget (σ p).path tab).toList.map fun o => (o.toList.map fun y => 60 * y.hd.len + 80).sum).sum + 200
  | op p q dst _, σ => 30 * p.length + 30 * q.length + 60 * dst.length + 30 * (σ p).len + 30 * (σ q).len + 200
  | bits p dst, σ => 30 * p.length + 60 * dst.length + (if σ p = .nil then 0 else (m + 1) * (60 * mb + 100)) + 200
  | check p, _ => 30 * p.length + 100

end DStep

/-- The program of a step; the argument is (step, trie); `n` is the length of guessed bit lists, in binary. -/
def dstepF (n : List Bool) : Fm := .ite (.hd (.hd .id))
  (.ite (.tl (.hd (.hd .id)))
    (.ite (.tl (.tl (.hd (.hd .id))))
      -- check
      (.ite (getF (.tl (.hd .id)) (.tl .id)) (.tl .id) .fail)
      -- bits
      (.ite (getF (.hd (.tl (.hd .id))) (.tl .id))
        (lett (.cons .id (bitsF n)) (setF (.tl (.tl (.hd (.hd .id)))) (.tl .id) (.tl (.hd .id))))
        (.tl .id)))
    -- op
    (setF (.hd (.tl (.tl (.tl (.hd .id)))))
      (getF (getF (.hd (.tl (.tl (.hd .id)))) (.tl .id))
        (getF (getF (.hd (.tl (.hd .id))) (.tl .id)) (.tl (.tl (.tl (.tl (.hd .id)))))))
      (.tl .id)))
  -- pick
  (lett (.cons .id (pickF (getF (getF (.hd (.tl (.hd .id))) (.tl .id)) (.tl (.tl (.hd .id))))))
    (assignF (.tl .id) (.tl (.hd .id))))

theorem len_ofBits (w : List Bool) : (ofBits w).len = w.length := by
  induction w with
  | nil => rfl
  | cons b w ih => simp [ofBits, len, ih]

theorem dstepF_does (n : List Bool) (st : DStep) (W : Tree) : ∃ Q,
    Does θ (dstepF n) (.cons st.tree W) Q (st.cost (KT.val n) n.length (gets W)) ∧
    (∀ q ∈ Q, gets q.2 ∈ st.exec (KT.val n) (gets W)) ∧
    ∀ Φ : (List Bool → Tree) → A, wsum Q (fun o => Φ (gets o)) = ((st.exec (KT.val n) (gets W)).map Φ).sum := by
  cases st with
  | check p =>
    have hg : Gives θ (getF (.tl (.hd .id)) (.tl .id)) (.cons (DStep.check p).tree W) (tget p W)
        (3 + 2 + 30 * p.length + 20) := by
      have := getF_gives (Gives.id (θ := θ) (.cons (DStep.check p).tree W)).hd.tl (Gives.id _).tl
      simp only [DStep.tree, hd_cons, tl_cons, path_ofBits, len_ofBits] at this ⊢
      exact this
    by_cases h : tget p W = .nil
    · rw [h] at hg
      refine ⟨[], ((Does.ite_true (Gives.id _).hd.hd (by simp [DStep.tree, num]) (Does.ite_true (Gives.id _).hd.hd.tl
        (by simp [DStep.tree, num]) (Does.ite_true (Gives.id _).hd.hd.tl.tl (by simp [DStep.tree, num])
        (Does.ite_false hg (Does.fail _)))))).mono ?_, by simp, fun Φ => ?_⟩
      · simp only [DStep.cost]
        omega
      · simp [DStep.exec, gets, h]
    · refine ⟨[(1, W)], ((Does.ite_true (Gives.id _).hd.hd (by simp [DStep.tree, num]) (Does.ite_true (Gives.id _).hd.hd.tl
        (by simp [DStep.tree, num]) (Does.ite_true (Gives.id _).hd.hd.tl.tl (by simp [DStep.tree, num])
        (Does.ite_true hg h (Gives.id _).tl))))).mono ?_, ?_, fun Φ => ?_⟩
      · simp only [DStep.cost]
        omega
      · intro q hq
        rw [List.mem_singleton] at hq
        subst hq
        simp [DStep.exec, gets, h]
      · simp [DStep.exec, gets, h]
  | bits p dst =>
    have hg : Gives θ (getF (.hd (.tl (.hd .id))) (.tl .id)) (.cons (DStep.bits p dst).tree W) (tget p W)
        (4 + 2 + 30 * p.length + 20) := by
      have := getF_gives (Gives.id (θ := θ) (.cons (DStep.bits p dst).tree W)).hd.tl.hd (Gives.id _).tl
      simp only [DStep.tree, hd_cons, tl_cons, path_ofBits, len_ofBits] at this ⊢
      exact this
    by_cases h : tget p W = .nil
    · rw [h] at hg
      refine ⟨[(1, W)], ((Does.ite_true (Gives.id _).hd.hd (by simp [DStep.tree, num]) (Does.ite_true (Gives.id _).hd.hd.tl
        (by simp [DStep.tree, num]) (Does.ite_false (Gives.id _).hd.hd.tl.tl
        (Does.ite_false hg (Gives.id _).tl))))).mono ?_, ?_, fun Φ => ?_⟩
      · simp only [DStep.cost, gets, h, if_true]
        omega
      · intro q hq
        rw [List.mem_singleton] at hq
        subst hq
        simp [DStep.exec, gets, h]
      · simp [DStep.exec, gets, h]
    · obtain ⟨Q, d, h1, h2⟩ := bitsF_does (θ := θ) n (.cons (DStep.bits p dst).tree W)
      have hs : ∀ q ∈ Q, Does θ (setF (.tl (.tl (.hd (.hd .id)))) (.tl .id) (.tl (.hd .id)))
          (.cons (.cons (DStep.bits p dst).tree W) q.2) [(1, tset dst q.2 W)] (5 + 2 + 3 + 60 * dst.length + 30) := by
        intro q _
        have := setF_gives (Gives.id (θ := θ) (.cons (.cons (DStep.bits p dst).tree W) q.2)).hd.hd.tl.tl (Gives.id _).tl
          (Gives.id _).hd.tl
        simp only [DStep.tree, hd_cons, tl_cons, path_ofBits, len_ofBits] at this ⊢
        exact this
      refine ⟨_, ((Does.ite_true (Gives.id _).hd.hd (by simp [DStep.tree, num]) (Does.ite_true (Gives.id _).hd.hd.tl
        (by simp [DStep.tree, num]) (Does.ite_false (Gives.id _).hd.hd.tl.tl
        (Does.ite_true hg h (Does.letk (R := fun o => [(1, tset dst o W)]) d hs)))))).mono ?_, ?_, fun Φ => ?_⟩
      · simp only [DStep.cost, gets, h, if_false]
        omega
      · intro q hq
        obtain ⟨q1, hq1, r, hr, e, -⟩ := mem_bindW hq
        rw [List.mem_singleton] at hr
        subst hr
        obtain ⟨u, hu, hu'⟩ := h1 q1 hq1
        rw [e, gets_tset, hu']
        simp only [DStep.exec, gets, h, if_false]
        exact List.mem_map.2 ⟨u, hu, rfl⟩
      · rw [wsum_bindW]
        simp only [wsum_cons, wsum_nil, one_mul, add_zero, gets_tset]
        rw [h2 fun o => Φ (Function.update (gets W) dst o)]
        simp [DStep.exec, gets, h, Function.comp_def]
  | op p q dst φ =>
    have hp : Gives θ (getF (.hd (.tl (.hd .id))) (.tl .id)) (.cons (DStep.op p q dst φ).tree W) (tget p W)
        (4 + 2 + 30 * p.length + 20) := by
      have := getF_gives (Gives.id (θ := θ) (.cons (DStep.op p q dst φ).tree W)).hd.tl.hd (Gives.id _).tl
      simp only [DStep.tree, hd_cons, tl_cons, path_ofBits, len_ofBits] at this ⊢
      exact this
    have hq : Gives θ (getF (.hd (.tl (.tl (.hd .id)))) (.tl .id)) (.cons (DStep.op p q dst φ).tree W) (tget q W)
        (5 + 2 + 30 * q.length + 20) := by
      have := getF_gives (Gives.id (θ := θ) (.cons (DStep.op p q dst φ).tree W)).hd.tl.tl.hd (Gives.id _).tl
      simp only [DStep.tree, hd_cons, tl_cons, path_ofBits, len_ofBits] at this ⊢
      exact this
    have hφ := getF_gives hq (getF_gives hp (Gives.id (θ := θ) (.cons (DStep.op p q dst φ).tree W)).hd.tl.tl.tl.tl)
    have hs := setF_gives (Gives.id (θ := θ) (.cons (DStep.op p q dst φ).tree W)).hd.tl.tl.tl.hd hφ (Gives.id _).tl
    simp only [DStep.tree, hd_cons, tl_cons, path_ofBits, len_ofBits] at hs
    refine ⟨[(1, tset dst (tget (tget q W).path (tget (tget p W).path φ)) W)], (Does.ite_true (Gives.id _).hd.hd
      (by simp [DStep.tree, num]) (Does.ite_false (Gives.id _).hd.hd.tl hs)).mono ?_, ?_, fun Φ => ?_⟩
    · simp only [DStep.cost, gets]
      omega
    · intro r hr
      rw [List.mem_singleton] at hr
      subst hr
      rw [gets_tset]
      simp [DStep.exec, gets]
    · simp only [wsum_cons, wsum_nil, one_mul, add_zero, gets_tset]
      simp [DStep.exec, gets]
  | pick p tab =>
    have hp : Gives θ (getF (.hd (.tl (.hd .id))) (.tl .id)) (.cons (DStep.pick p tab).tree W) (tget p W)
        (4 + 2 + 30 * p.length + 20) := by
      have := getF_gives (Gives.id (θ := θ) (.cons (DStep.pick p tab).tree W)).hd.tl.hd (Gives.id _).tl
      simp only [DStep.tree, hd_cons, tl_cons, path_ofBits, len_ofBits] at this ⊢
      exact this
    have hl := getF_gives hp (Gives.id (θ := θ) (.cons (DStep.pick p tab).tree W)).hd.tl.tl
    obtain ⟨opts, ho⟩ : ∃ l, l = (tget (tget p W).path tab).toList := ⟨_, rfl⟩
    have hl' : Gives θ (getF (getF (.hd (.tl (.hd .id))) (.tl .id)) (.tl (.tl (.hd .id)))) (.cons (DStep.pick p tab).tree W)
        (listT opts) (4 + 2 + 30 * p.length + 20 + 4 + 30 * (tget p W).len + 20) := by
      rw [ho, listT_toList]
      exact hl
    have hpk := pickF_does hl'
    have hs : ∀ q ∈ opts.map fun x => ((1 : A), x), Does θ (assignF (.tl .id) (.tl (.hd .id)))
        (.cons (.cons (DStep.pick p tab).tree W) q.2) [(1, assignT W q.2)]
        (2 + 3 + (opts.map fun o => (o.toList.map fun y => 60 * y.hd.len + 80).sum).sum + 20) := by
      intro q hq
      rw [List.mem_map] at hq
      obtain ⟨o, ho', rfl⟩ := hq
      refine (assignF_gives (Gives.id _).tl (Gives.id _).hd.tl).mono ?_
      have := List.single_le_sum (l := opts.map fun o => (o.toList.map fun y => 60 * y.hd.len + 80).sum)
        (fun _ _ => Nat.zero_le _) _ (List.mem_map.2 ⟨o, ho', rfl⟩)
      simp only [tl_cons]
      omega
    refine ⟨_, (Does.ite_false (Gives.id _).hd.hd (Does.letk (R := fun o => [(1, assignT W o)]) hpk hs)).mono ?_, ?_,
      fun Φ => ?_⟩
    · simp only [DStep.cost, gets, ← ho]
      omega
    · intro r hr
      obtain ⟨q1, hq1, r', hr', e, -⟩ := mem_bindW hr
      rw [List.mem_singleton] at hr'
      subst hr'
      rw [List.mem_map] at hq1
      obtain ⟨o, ho', rfl⟩ := hq1
      rw [e, gets_assign]
      simp only [DStep.exec, gets, ← ho]
      exact List.mem_map.2 ⟨o, ho', rfl⟩
    · rw [wsum_bindW]
      simp only [wsum_cons, wsum_nil, one_mul, add_zero, gets_assign]
      simp [DStep.exec, gets, ← ho, wsum, Function.comp_def]

/-- The states after a list of steps. -/
def execAll (m : ℕ) : List DStep → (List Bool → Tree) → List (List Bool → Tree)
  | [], σ => [σ]
  | st :: sts, σ => (st.exec m σ).flatMap (execAll m sts)

theorem sum_execAll_cons (m : ℕ) (st : DStep) (sts : List DStep) (σ : List Bool → Tree) (Φ : (List Bool → Tree) → A) :
    ((execAll m (st :: sts) σ).map Φ).sum = ((st.exec m σ).map fun σ' => ((execAll m sts σ').map Φ).sum).sum := by
  rw [execAll, sum_flatMap_map]

theorem execAll_append (m : ℕ) (sts sts' : List DStep) (σ : List Bool → Tree) :
    execAll m (sts ++ sts') σ = (execAll m sts σ).flatMap (execAll m sts') := by
  induction sts generalizing σ with
  | nil => simp [execAll]
  | cons st sts ih =>
    rw [List.cons_append, execAll, execAll, List.flatMap_assoc]
    exact List.flatMap_congr fun σ' _ => ih σ'

/-- All steps: `w` gives the trie. -/
def dstepsF (n : List Bool) (sts : List DStep) (w : Fm) : Fm :=
  foldF (dstepF n) w (.quote (listT (sts.map DStep.tree)))

theorem dstepsF_does (n : List Bool) (sts : List DStep) {wf : Fm} {x W : Tree} {cw : ℕ} (hw : Gives θ wf x W cw)
    {I : List DStep → (List Bool → Tree) → Prop} {c : DStep → ℕ}
    (hI : ∀ st sts' σ, I (st :: sts') σ → st.cost (KT.val n) n.length σ ≤ c st ∧
      ∀ σ' ∈ st.exec (KT.val n) σ, I sts' σ') (hW : I sts (gets W)) : ∃ Q,
    Does θ (dstepsF n sts wf) x Q (cw + (sts.map fun st => c st + 30).sum + 30) ∧
    (∀ q ∈ Q, gets q.2 ∈ execAll (KT.val n) sts (gets W)) ∧
    ∀ Φ : (List Bool → Tree) → A, wsum Q (fun o => Φ (gets o)) = ((execAll (KT.val n) sts (gets W)).map Φ).sum := by
  choose f hf1 hf2 hf3 using fun st W => dstepF_does (θ := θ) n st W
  -- a function of trees
  classical
  let F : Tree → Tree → List (A × Tree) := fun t W => if h : ∃ st : DStep, st.tree = t then f h.choose W else []
  have hF : ∀ st : DStep, ∃ st' : DStep, st'.tree = st.tree ∧ ∀ W, F st.tree W = f st' W := by
    intro st
    have h : ∃ st' : DStep, st'.tree = st.tree := ⟨st, rfl⟩
    exact ⟨h.choose, h.choose_spec, fun W => dif_pos h⟩
  have hinj : ∀ st st' : DStep, st.tree = st'.tree → st = st' := by
    have hob : ∀ a b : List Bool, ofBits a = ofBits b → a = b := fun a b h => by
      rw [← path_ofBits a, h, path_ofBits]
    intro st st' h
    cases st <;> cases st' <;> simp only [DStep.tree, Tree.cons.injEq, num] at h <;>
      simp only [reduceCtorEq, false_and, and_false, true_and, and_true, Tree.cons.injEq] at h
    · rw [hob _ _ h.1, h.2]
    · rw [hob _ _ h.1, hob _ _ h.2.1, hob _ _ h.2.2.1, h.2.2.2]
    · rw [hob _ _ h.1, hob _ _ h.2]
    · rw [hob _ _ h]
  have hF' : ∀ (st : DStep) W, F st.tree W = f st W := by
    intro st W
    obtain ⟨st', h1, h2⟩ := hF st
    rw [h2, hinj _ _ h1]
  have hsum : ∀ (sts : List DStep) (W : Tree) (Φ : (List Bool → Tree) → A),
      wsum (foldW F (sts.map DStep.tree) W) (fun o => Φ (gets o)) = ((execAll (KT.val n) sts (gets W)).map Φ).sum := by
    intro sts
    induction sts with
    | nil =>
      intro W Φ
      simp [foldW, execAll]
    | cons st sts ih =>
      intro W Φ
      rw [List.map_cons, foldW, wsum_bindW, sum_execAll_cons, ← hf3 st W, hF']
      exact wsum_congr fun q _ => ih q.2 Φ
  have hmem : ∀ (sts : List DStep) (W : Tree), ∀ q ∈ foldW F (sts.map DStep.tree) W,
      gets q.2 ∈ execAll (KT.val n) sts (gets W) := by
    intro sts
    induction sts with
    | nil =>
      intro W q hq
      simp only [List.map_nil, foldW, List.mem_singleton] at hq
      subst hq
      simp [execAll]
    | cons st sts ih =>
      intro W q hq
      rw [List.map_cons, foldW] at hq
      obtain ⟨q1, hq1, r, hr, e, -⟩ := mem_bindW hq
      rw [hF'] at hq1
      rw [e, execAll, List.mem_flatMap]
      exact ⟨_, hf2 st W q1 hq1, ih q1.2 r hr⟩
  let d : Tree → ℕ := fun t => if h : ∃ st : DStep, st.tree = t then c h.choose else 0
  have hd : ∀ st : DStep, d st.tree = c st := by
    intro st
    have h : ∃ st' : DStep, st'.tree = st.tree := ⟨st, rfl⟩
    have h1 : d st.tree = c h.choose := dif_pos h
    rw [h1, hinj _ _ h.choose_spec]
  have hfold := foldF_does (f := F) (xs := sts.map DStep.tree) (d := d)
    (Inv := fun ys W => ∃ sts' : List DStep, ys = sts'.map DStep.tree ∧ I sts' (gets W)) hw
    (Gives.quote (θ := θ) (listT (sts.map DStep.tree)) x) (step := dstepF n) (by
      rintro t ys W - ⟨sts', h1, h2⟩
      cases sts' with
      | nil => simp at h1
      | cons st sts' =>
        rw [List.map_cons, List.cons.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        obtain ⟨h3, h4⟩ := hI st sts' _ h2
        rw [hF', hd]
        exact ⟨(hf1 st W).mono h3, fun q hq => ⟨sts', rfl, h4 _ (hf2 st W q hq)⟩⟩) ⟨sts, rfl, hW⟩
  refine ⟨_, hfold.mono ?_, hmem sts W, hsum sts W⟩
  rw [List.map_map]
  have e : (sts.map ((fun x => d x + 30) ∘ DStep.tree)) = sts.map fun st => c st + 30 :=
    List.map_congr_left fun st _ => by simp only [Function.comp_apply, hd]
  rw [e]
  omega

section Templates

/-- Templates. -/
inductive Tm where
  /-- a fixed tree -/
  | c (t : Tree)
  /-- the value at a path -/
  | get (p : List Bool)
  /-- a node -/
  | cons (a b : Tm)
  /-- `a` if the value at `p` is `t`, else `b` -/
  | ifeq (p : List Bool) (t : Tree) (a b : Tm)
  /-- concatenation of lists -/
  | app (a b : Tm)

namespace Tm

/-- As a tree. -/
def tree : Tm → Tree
  | c t => .cons (num 0) t
  | get p => .cons (num 1) (ofBits p)
  | cons a b => .cons (num 2) (.cons a.tree b.tree)
  | ifeq p t a b => .cons (num 3) (.cons (ofBits p) (.cons t (.cons a.tree b.tree)))
  | app a b => .cons (num 4) (.cons a.tree b.tree)

/-- Fill in the values. -/
def expand (σ : List Bool → Tree) : Tm → Tree
  | c t => t
  | get p => σ p
  | cons a b => .cons (a.expand σ) (b.expand σ)
  | ifeq p t a b => if σ p = t then a.expand σ else b.expand σ
  | app a b => listT ((a.expand σ).toList ++ (b.expand σ).toList)

/-- The cost. -/
def cost (σ : List Bool → Tree) : Tm → ℕ
  | c _ => 20
  | get p => 30 * p.length + 50
  | cons a b => a.cost σ + b.cost σ + 100
  | ifeq p _ a b => 30 * p.length + 60 * (σ p).size + (if σ p = .nil then 0 else 0) + a.cost σ + b.cost σ + 200
  | app a b => a.cost σ + b.cost σ + 62 * (a.expand σ).toList.length + 250

end Tm

/-- Recursive call of the expansion. -/
def tmRec (t : Fm) : Fm := .run (.hd .id) (.cons (.hd .id) (.cons t (.tl (.tl .id))))

/-- The program that fills in templates. The argument is (this program, (template, trie)). -/
def tmB : Fm := .ite (.hd (.hd (.tl .id)))
  (.ite (.tl (.hd (.hd (.tl .id))))
    (.ite (.tl (.tl (.hd (.hd (.tl .id)))))
      (.ite (.tl (.tl (.tl (.hd (.hd (.tl .id))))))
        (appF (tmRec (.hd (.tl (.hd (.tl .id))))) (tmRec (.tl (.tl (.hd (.tl .id))))))
        (.ite (eqF (getF (.hd (.tl (.hd (.tl .id)))) (.tl (.tl .id))) (.hd (.tl (.tl (.hd (.tl .id))))))
          (tmRec (.hd (.tl (.tl (.tl (.hd (.tl .id))))))) (tmRec (.tl (.tl (.tl (.tl (.hd (.tl .id)))))))))
      (.cons (tmRec (.hd (.tl (.hd (.tl .id))))) (tmRec (.tl (.tl (.hd (.tl .id)))))))
    (getF (.tl (.hd (.tl .id))) (.tl (.tl .id))))
  (.tl (.hd (.tl .id)))

theorem tmRec_gives {t : Fm} {x s W o : Tree} {ct d : ℕ} (ht : Gives θ t (.cons tmB.code (.cons x W)) s ct)
    (h : Gives θ tmB (.cons tmB.code (.cons s W)) o d) :
    Gives θ (tmRec t) (.cons tmB.code (.cons x W)) o (ct + d + 15) := by
  refine (Gives.run (Gives.id (θ := θ) (.cons tmB.code (.cons x W))).hd (Gives.cons (Gives.id _).hd
    (Gives.cons ht (Gives.id _).tl.tl)) (by rw [hd_cons, Fm.ofTree_code]; exact h)).mono (by omega)

theorem tmB_gives (t : Tm) (W : Tree) :
    Gives θ tmB (.cons tmB.code (.cons t.tree W)) (t.expand (gets W)) (t.cost (gets W)) := by
  induction t with
  | c t =>
    exact ((Gives.id _).tl.hd.hd.ite_false (Gives.id _).tl.hd.tl).mono (by simp [Tm.cost])
  | get p =>
    have hg := getF_gives (Gives.id (θ := θ) (.cons tmB.code (.cons (Tm.get p).tree W))).tl.hd.tl (Gives.id _).tl.tl
    simp only [Tm.tree, hd_cons, tl_cons, path_ofBits, len_ofBits] at hg
    refine ((Gives.id _).tl.hd.hd.ite_true (by simp [Tm.tree, num]) ((Gives.id _).tl.hd.hd.tl.ite_false hg)).mono ?_
    simp only [Tm.cost]
    omega
  | cons a b iha ihb =>
    have ha := tmRec_gives (Gives.id (θ := θ) (.cons tmB.code (.cons (Tm.cons a b).tree W))).tl.hd.tl.hd iha
    have hb := tmRec_gives (Gives.id (θ := θ) (.cons tmB.code (.cons (Tm.cons a b).tree W))).tl.hd.tl.tl ihb
    refine ((Gives.id _).tl.hd.hd.ite_true (by simp [Tm.tree, num]) ((Gives.id _).tl.hd.hd.tl.ite_true
      (by simp [Tm.tree, num]) ((Gives.id _).tl.hd.hd.tl.tl.ite_false (Gives.cons ha hb)))).mono ?_
    simp only [Tm.cost]
    omega
  | ifeq p t a b iha ihb =>
    have ha := tmRec_gives (Gives.id (θ := θ) (.cons tmB.code (.cons (Tm.ifeq p t a b).tree W))).tl.hd.tl.tl.tl.hd iha
    have hb := tmRec_gives (Gives.id (θ := θ) (.cons tmB.code (.cons (Tm.ifeq p t a b).tree W))).tl.hd.tl.tl.tl.tl ihb
    have hg := getF_gives (Gives.id (θ := θ) (.cons tmB.code (.cons (Tm.ifeq p t a b).tree W))).tl.hd.tl.hd (Gives.id _).tl.tl
    simp only [Tm.tree, hd_cons, tl_cons, path_ofBits, len_ofBits] at hg
    have he := eqF_gives hg (Gives.id (θ := θ) (.cons tmB.code (.cons (Tm.ifeq p t a b).tree W))).tl.hd.tl.tl.hd
    have e0 : (Tm.ifeq p t a b).expand (gets W) = if tget p W = t then a.expand (gets W) else b.expand (gets W) := rfl
    have hc : (Tm.ifeq p t a b).cost (gets W) = 30 * p.length + 60 * (tget p W).size + (if gets W p = .nil then 0 else 0) +
      a.cost (gets W) + b.cost (gets W) + 200 := rfl
    have hc0 : (if gets W p = .nil then 0 else 0) = 0 := by split_ifs <;> rfl
    rw [e0]
    by_cases h : tget p W = t
    · rw [if_pos h]
      have hb' : bit (decide (tget p W = t)) ≠ .nil := by simp [h, bit, one]
      refine ((Gives.id _).tl.hd.hd.ite_true (by simp [Tm.tree, num]) ((Gives.id _).tl.hd.hd.tl.ite_true
        (by simp [Tm.tree, num]) ((Gives.id _).tl.hd.hd.tl.tl.ite_true (by simp [Tm.tree, num])
        ((Gives.id _).tl.hd.hd.tl.tl.tl.ite_false (Gives.ite_true he hb' ha))))).mono ?_
      rw [hc, hc0]
      omega
    · rw [if_neg h]
      have hb' : bit (decide (tget p W = t)) = .nil := by simp [h, bit]
      rw [show (Tree.cons tmB.code (.cons (Tm.ifeq p t a b).tree W)).tl.hd.tl.tl.hd = t from rfl, hb'] at he
      refine ((Gives.id _).tl.hd.hd.ite_true (by simp [Tm.tree, num]) ((Gives.id _).tl.hd.hd.tl.ite_true
        (by simp [Tm.tree, num]) ((Gives.id _).tl.hd.hd.tl.tl.ite_true (by simp [Tm.tree, num])
        ((Gives.id _).tl.hd.hd.tl.tl.tl.ite_false (Gives.ite_false he hb))))).mono ?_
      rw [hc, hc0]
      omega
  | app a b iha ihb =>
    have ha := tmRec_gives (Gives.id (θ := θ) (.cons tmB.code (.cons (Tm.app a b).tree W))).tl.hd.tl.hd iha
    have hb := tmRec_gives (Gives.id (θ := θ) (.cons tmB.code (.cons (Tm.app a b).tree W))).tl.hd.tl.tl ihb
    rw [← listT_toList (a.expand (gets W))] at ha
    rw [← listT_toList (b.expand (gets W))] at hb
    have happ := appF_gives ha hb
    refine ((Gives.id _).tl.hd.hd.ite_true (by simp [Tm.tree, num]) ((Gives.id _).tl.hd.hd.tl.ite_true
      (by simp [Tm.tree, num]) ((Gives.id _).tl.hd.hd.tl.tl.ite_true (by simp [Tm.tree, num])
      ((Gives.id _).tl.hd.hd.tl.tl.tl.ite_true (by simp [Tm.tree, num]) happ)))).mono ?_
    simp only [Tm.cost]
    omega

/-- Fill in a template: `t` gives the template, `w` the trie. -/
def tmF (t w : Fm) : Fm := app tmB.code (.cons (.quote tmB.code) (.cons t w))

theorem tmF_gives {tf wf : Fm} {x W : Tree} {ct cw : ℕ} {t : Tm} (ht : Gives θ tf x t.tree ct) (hw : Gives θ wf x W cw) :
    Gives θ (tmF tf wf) x (t.expand (gets W)) (ct + cw + t.cost (gets W) + 10) := by
  refine (Gives.app (p := tmB.code) (Gives.cons (Gives.quote _ _) (Gives.cons ht hw)) (by
    rw [Fm.ofTree_code]
    exact tmB_gives t W)).mono (by omega)

/-- Fill in all templates of a list. -/
def tmsF (ts : List Tm) (w : Fm) : Fm := mapF (tmF (.tl .id) (.hd .id)) w (.quote (listT (ts.map Tm.tree)))

theorem tmsF_gives {wf : Fm} {x W : Tree} {cw c : ℕ} {ts : List Tm} (hw : Gives θ wf x W cw)
    (hc : ∀ t ∈ ts, t.cost (gets W) ≤ c) :
    Gives θ (tmsF ts wf) x (listT (ts.map fun t => t.expand (gets W))) (cw + ts.length * (c + 60) + 30) := by
  classical
  let g : Tree → Tree := fun y => if h : ∃ t ∈ ts, t.tree = y then h.choose.expand (gets W) else .nil
  have hg : ∀ y ∈ ts.map Tm.tree, ∃ t ∈ ts, t.tree = y ∧ g y = t.expand (gets W) := by
    intro y hy
    rw [List.mem_map] at hy
    obtain ⟨t, ht, rfl⟩ := hy
    have h : ∃ t' ∈ ts, t'.tree = t.tree := ⟨t, ht, rfl⟩
    exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2, dif_pos h⟩
  have hall : ∀ t ∈ ts, g t.tree = t.expand (gets W) := by
    intro t ht
    obtain ⟨t', ht', h1, h2⟩ := hg t.tree (List.mem_map.2 ⟨t, ht, rfl⟩)
    rw [h2]
    have e1 := tmB_gives (θ := fun _ => (0 : ℤ)) t W
    have e2 := tmB_gives (θ := fun _ => (0 : ℤ)) t' W
    rw [h1] at e2
    -- both are the value of the program at the same tree
    have h3 := e1.evl.2 fun o => if o = t.expand (gets W) then 1 else 0
    have h4 := e2.evl.2 fun o => if o = t.expand (gets W) then 1 else 0
    rw [h3] at h4
    simp only [wsum_cons, wsum_nil, if_true, mul_one, add_zero, one_mul] at h4
    by_contra hne
    rw [if_neg hne] at h4
    exact one_ne_zero h4
  have := mapF_gives (step := tmF (.tl .id) (.hd .id)) (g := g) (d := fun _ => c + 20) (xs := ts.map Tm.tree) hw
    (Gives.quote (θ := θ) (listT (ts.map Tm.tree)) x) (by
      intro y hy
      obtain ⟨t, ht, rfl, h2⟩ := hg y hy
      rw [h2]
      refine (tmF_gives (t := t) (Gives.id _).tl (Gives.id _).hd).mono ?_
      have := hc t ht
      simp only [hd_cons]
      omega)
  rw [List.map_map] at this
  have e : ts.map (g ∘ Tm.tree) = ts.map fun t => t.expand (gets W) := List.map_congr_left fun t ht => hall t ht
  rw [e] at this
  refine this.mono ?_
  rw [List.map_const', List.sum_replicate, smul_eq_mul, List.length_map]
  have e2 : ts.length * (c + 20 + 40) = ts.length * (c + 60) := by ring
  omega

end Templates

end NS1
