/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.Closure.Basic

/-! Closure of polynomial time under case distinctions on Bool, Option, sums and lists; the branches
may use the context x.
Two fragments do all the work: one takes a sum apart and goes on according to its tag, the other
puts a tag on a list that
tells whether it is empty. All else follows by composition, because a fragment sees the tree of a
value and not its type. -/

@[expose] public section

namespace Groundwork.PolyT

open TM Turing

variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

/-! ### A choice between two fragments -/

/-- The head statement leads to the label b; then the fragment for b runs. -/
theorem within_branch {q : TM2.Stmt (fun _ : Stk => Sym) Bool (Option Sym)} {P Q : Fr} {S S₁ S' : Stk → List Sym} {t : ℕ}
    (b : Bool) (h : TM2.stepAux q none S = ⟨some b, none, S₁⟩) (hb : (bif b then P else Q).Within S₁ t S') :
    (Frag.branch q P Q).Within S (t + 1) S' := by
  obtain ⟨n, hn, hr⟩ := hb
  cases b
  · exact ⟨n + 1, by omega, Frag.branch_runs_false h hr⟩
  · exact ⟨n + 1, by omega, Frag.branch_runs_true h hr⟩

/-- Pop the bit on top of the main stack and go to the label of that name. -/
def tagHead : TM2.Stmt (fun _ : Stk => Sym) Bool (Option Sym) :=
  .pop .main (fun _ o => o) <|
    .branch (fun s => s == some (.bit true)) (.load (fun _ => none) <| .goto fun _ => true)
      (.load (fun _ => none) <| .goto fun _ => false)

theorem tagHead_eq (b : Bool) (M A B N : List Sym) :
    TM2.stepAux tagHead none (st (.bit b :: M) A B N) = ⟨some b, none, st M A B N⟩ := by
  have h : (some (Sym.bit false) == some (Sym.bit true)) = false := by decide
  cases b <;> simp [tagHead, TM2.stepAux, h]

/-- Case distinction on a sum, without context. -/
theorem sumCore {f : β → δ} {g : γ → δ} (hf : PolyT f) (hg : PolyT g) : PolyT (fun s : β ⊕ γ => s.elim f g) := by
  obtain ⟨P, t, htp, htm, hP, hPl⟩ := hf.elim
  obtain ⟨Q, q, hqp, hqm, hQ, hQl⟩ := hg.elim
  -- the tag true stands for inr, so g's fragment Q is the branch of the label true
  refine PolyT.of (unconsF.seq (Frag.branch tagHead Q P)) (t := fun n => (2 * n + 6) + (t n + q n + 1))
    (s := fun n => t n + q n) ?_ (htp.add hqp) (fun x M A B N => ?_) (fun x => ?_)
  · exact (((PB.const 2).mul PB.id').add (PB.const 6)).add ((htp.add hqp).add (PB.const 1))
  · cases x with
    | inl y =>
      have hl : len (Sum.inl y : β ⊕ γ) = len y + 3 := by simp [len, wd, Enc.toV, code]
      have c1 := unconsF_within (.bit false) (Enc.toV y) M A B N
      have c2 := within_branch (P := Q) (Q := P) false (tagHead_eq false (wd y ++ M) A B N) (hP y M A B N)
      refine (c1.seq c2).mono ?_
      have h1 : (code (.bit false)).length = 1 := rfl
      have h2 : (code (Enc.toV y)).length = len y := rfl
      have h3 : t (len y) ≤ t (len y + 3) := htm (by omega)
      simp only [hl, h1, h2]
      omega
    | inr z =>
      have hl : len (Sum.inr z : β ⊕ γ) = len z + 3 := by simp [len, wd, Enc.toV, code]
      have c1 := unconsF_within (.bit true) (Enc.toV z) M A B N
      have c2 := within_branch (P := Q) (Q := P) true (tagHead_eq true (wd z ++ M) A B N) (hQ z M A B N)
      refine (c1.seq c2).mono ?_
      have h1 : (code (.bit true)).length = 1 := rfl
      have h2 : (code (Enc.toV z)).length = len z := rfl
      have h3 : q (len z) ≤ q (len z + 3) := hqm (by omega)
      simp only [hl, h1, h2]
      omega
  · cases x with
    | inl y =>
      have hl : len (Sum.inl y : β ⊕ γ) = len y + 3 := by simp [len, wd, Enc.toV, code]
      have h3 : t (len y) ≤ t (len y + 3) := htm (by omega)
      have h4 := hPl y
      simp only [hl, Sum.elim_inl]
      omega
    | inr z =>
      have hl : len (Sum.inr z : β ⊕ γ) = len z + 3 := by simp [len, wd, Enc.toV, code]
      have h3 : q (len z) ≤ q (len z + 3) := hqm (by omega)
      have h4 := hQl z
      simp only [hl, Sum.elim_inr]
      omega

/-! ### Is the list empty? -/

/-- Look at the second symbol of the item on top of the main stack: a closing bracket means that the
item is ⟨⟩ (label false),
anything else that it is a pair (label true). The stack is left as it was (the first symbol, an
opening bracket, is popped
and pushed back). -/
def nilHead : TM2.Stmt (fun _ : Stk => Sym) Bool (Option Sym) :=
  .pop .main (fun _ _ => none) <| .peek .main (fun _ o => o) <| .push .main (fun _ => .L) <|
    .branch (fun s => s == some .R) (.load (fun _ => none) <| .goto fun _ => false)
      (.load (fun _ => none) <| .goto fun _ => true)

theorem nilHead_nil (M A B N : List Sym) :
    TM2.stepAux nilHead none (st (.L :: .R :: M) A B N) = ⟨some false, none, st (.L :: .R :: M) A B N⟩ := by
  simp [nilHead, TM2.stepAux]

theorem nilHead_cons (x : V) (M A B N : List Sym) :
    TM2.stepAux nilHead none (st (.L :: (code x ++ M)) A B N) = ⟨some true, none, st (.L :: (code x ++ M)) A B N⟩ := by
  cases x <;> simp [nilHead, TM2.stepAux, code]

/-- Put the tag b on the item on top of the main stack. -/
def tagF (b : Bool) : Fr := (pushW [.bit b]).seq consF

theorem tagF_within (b : Bool) (x : V) (M A B N : List Sym) :
    (tagF b).Within (st (code x ++ M) A B N) (2 * (code x).length + 9) (st (code (.cons (.bit b) x) ++ M) A B N) := by
  have c1 := pushW_within (code x ++ M) A B N [.bit b]
  have c2 := consF_within (.bit b) x M A B N
  refine (c1.seq c2).mono ?_
  have h1 : (code (.bit b)).length = 1 := rfl
  omega

/-- A list is empty, or it has a first element and a rest. -/
def listSplit : List β → Unit ⊕ β × List β
  | [] => .inl ()
  | e :: r => .inr (e, r)

theorem listSplit_poly : PolyT (listSplit : List β → Unit ⊕ β × List β) := by
  refine PolyT.of (Frag.branch nilHead (tagF true) (tagF false)) (t := fun n => 2 * n + 9 + 1) (s := fun n => n + 3)
    ?_ ?_ (fun l M A B N => ?_) (fun l => ?_)
  · exact (((PB.const 2).mul PB.id').add (PB.const 9)).add (PB.const 1)
  · exact PB.id'.add (PB.const 3)
  · cases l with
    | nil => exact within_branch false (nilHead_nil M A B N) (tagF_within false .nil M A B N)
    | cons e r =>
      have h := nilHead_cons (Enc.toV e) (wd r ++ [.R] ++ M) A B N
      have e0 : wd (e :: r) ++ M = .L :: (code (Enc.toV e) ++ (wd r ++ [.R] ++ M)) := by
        simp [wd, Enc.toV, code]
      have c := tagF_within true (Enc.toV (e :: r)) M A B N
      rw [← e0] at h
      exact within_branch true h c
  · cases l with
    | nil => simp [len, wd, Enc.toV, code, listSplit]
    | cons e r => simp [len, wd, Enc.toV, code, listSplit]; omega

/-! ### The case distinctions -/

/-- Case distinction on a Boolean c x; both branches see the context x. -/
@[fun_prop] theorem cond' {c : α → Bool} {f g : α → β} (hc : PolyT c) (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => bif c x then f x else g x) := by
  have h1 : PolyT (fun p : Bool × α => (bif p.1 then Sum.inr p.2 else Sum.inl p.2 : α ⊕ α)) :=
    of_wd (f := fun p : Bool × α => p) id' id (fun _ => rfl) (fun p => by rcases p with ⟨_ | _, x⟩ <;> rfl)
  exact (comp (sumCore hg hf) (comp h1 (prodMk hc id'))).congr (fun x => by dsimp only; cases c x <;> rfl)
/-- The same for `if … then … else` on a decidable proposition c x. -/
@[fun_prop] theorem ite' {c : α → Prop} [DecidablePred c] {f g : α → β} (hc : PolyT fun x => decide (c x)) (hf : PolyT f)
    (hg : PolyT g) : PolyT (fun x => if c x then f x else g x) :=
  (cond' hc hf hg).congr (fun x => by by_cases h : c x <;> simp [h])
/-- Case distinction on a sum s x; each branch sees the context x and what lies under the tag. -/
@[fun_prop] theorem sumElim {s : α → β ⊕ γ} {f : α → β → δ} {g : α → γ → δ} (hs : PolyT s)
    (hf : PolyT fun p : α × β => f p.1 p.2) (hg : PolyT fun p : α × γ => g p.1 p.2) :
    PolyT (fun x => (s x).elim (f x) (g x)) := by
  -- a sum is a pair of a bit and a tree; hand the context to what lies under the tag
  let _ : Enc V := ⟨id⟩
  have hd : PolyT (fun p : (β ⊕ γ) × α =>
      (p.1.elim (fun y => Sum.inl (p.2, y)) (fun z => Sum.inr (p.2, z)) : α × β ⊕ α × γ)) :=
    of_wd (f := fun q : (Bool × V) × α => (q.1.1, (q.2, q.1.2))) (by fun_prop)
      (fun p => ((p.1.elim (fun _ => false) (fun _ => true), p.1.elim Enc.toV Enc.toV), p.2))
      (fun p => by rcases p with ⟨y | z, x⟩ <;> rfl) (fun p => by rcases p with ⟨y | z, x⟩ <;> rfl)
  exact (comp (sumCore hf hg) (comp hd (prodMk hs id'))).congr (fun x => by dsimp only; cases s x <;> rfl)
/-- Case distinction on a list l x: it is empty, or it has a first element and a rest; both branches
see the context x. -/
theorem listCases {l : α → List β} {d : α → γ} {f : α → β → List β → γ} (hl : PolyT l) (hd : PolyT d)
    (hf : PolyT fun p : α × β × List β => f p.1 p.2.1 p.2.2) :
    PolyT (fun x => match l x with | [] => d x | e :: r => f x e r) :=
  (sumElim (f := fun x _ => d x) (g := fun x q => f x q.1 q.2) (comp listSplit_poly hl) (comp hd (fst id')) hf).congr
    (fun x => by cases l x <;> rfl)
/-- Case distinction on an option o x; both branches see the context x. -/
@[fun_prop] theorem optionElim {o : α → Option β} {d : α → γ} {f : α → β → γ} (ho : PolyT o) (hd : PolyT d)
    (hf : PolyT fun p : α × β => f p.1 p.2) : PolyT (fun x => (o x).elim (d x) (f x)) := by
  -- an option has the tree of the list of its elements
  have h1 : PolyT (fun x => (o x).toList) :=
    of_wd ho id (fun _ => rfl) (fun x => by show wd (o x).toList = wd (o x); cases o x <;> rfl)
  have h2 : PolyT fun p : α × β × List β => f p.1 p.2.1 :=
    comp (g := fun p : α × β × List β => (p.1, p.2.1)) hf (by fun_prop)
  exact (listCases (f := fun x e _ => f x e) h1 hd h2).congr (fun x => by cases o x <;> rfl)

end Groundwork.PolyT
