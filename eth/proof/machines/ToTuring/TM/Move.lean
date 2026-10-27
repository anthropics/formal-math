/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.TM.Rename
public import ToTuring.TM.Stacks

/-! The one loop that handles data: pop one item (the code of a tree) off a stack, symbol by symbol,
and push its mirror
image on no, one or two other stacks. Open brackets are counted in unary on the counter stack (one
`R` for each open bracket)
above a sentinel `L`, so that nothing beneath the item, nor beneath the sentinel, is ever looked at.
The loop is written once,
for four stacks (source, two targets, counter) with two flags that say which targets are used; `mv`,
`mv2` and `drp` are that
loop on renamed stacks (TM/Rename.lean). -/

@[expose] public section

namespace Groundwork.TM

open Turing

/-- Source, two targets, counter. -/
inductive S4 | src | t1 | t2 | cnt
  deriving DecidableEq

/-- The labels of the loop. -/
inductive MvL | start | loop
  deriving DecidableEq

instance : Fintype MvL := ⟨{.start, .loop}, fun x => by cases x <;> simp⟩

/-- Statements of the loop. -/
abbrev St4 := TM2.Stmt (fun _ : S4 => Sym) MvL (Option Sym)

/-- Push on k if p. -/
def pushIf (p : Bool) (k : S4) (f : Option Sym → Sym) (q : St4) : St4 := if p then .push k f q else q

/-- Is the count back at the sentinel? Then remove it and halt; else go on. -/
def mvChk : St4 :=
  .peek .cnt (fun _ o => o) <|
    .branch (fun s => s == some .L) (.pop .cnt (fun _ _ => none) .halt) (.load (fun _ => none) <| .goto fun _ => .loop)

/-- The program: a sentinel on the counter; then pop a symbol, push its mirror image (on t1 if p₁,
on t2 if p₂), count. -/
def mvM (p₁ p₂ : Bool) : MvL → St4
  | .start => .push .cnt (fun _ => .L) <| .goto fun _ => .loop
  | .loop => .pop .src (fun _ o => o) <|
      .branch (fun s => s == some .L)
        (pushIf p₁ .t1 (fun _ => .R) <| pushIf p₂ .t2 (fun _ => .R) <| .push .cnt (fun _ => .R) <|
          .load (fun _ => none) <| .goto fun _ => .loop)
        (.branch (fun s => s == some .R)
          (pushIf p₁ .t1 (fun _ => .L) <| pushIf p₂ .t2 (fun _ => .L) <| .pop .cnt (fun s _ => s) mvChk)
          (pushIf p₁ .t1 (fun s => s.getD .L) <| pushIf p₂ .t2 (fun s => s.getD .L) mvChk))

/-- The loop as a fragment on four stacks. -/
def mvB (p₁ p₂ : Bool) : Frag (fun _ : S4 => Sym) (Option Sym) := ⟨MvL, .start, mvM p₁ p₂⟩

/-- The four stacks of the loop as work stacks. -/
def toStk (i j k : Stk) : S4 → Stk
  | .src => i
  | .t1 => j
  | .t2 => k
  | .cnt => .cnt

/-- A work stack other than i, j and the counter; it fills a target slot of the loop that is not
used. -/
def other (i j : Stk) : Stk :=
  if i ≠ .main ∧ j ≠ .main then .main else if i ≠ .a ∧ j ≠ .a then .a else .b

/-- Move one item from stack i to stack j, mirrored. -/
def mv (i j : Stk) : Fr := (mvB true false).ren (toStk i j (other i j))

/-- Move one item from stack i to the stacks j and k, mirrored. -/
def mv2 (i j k : Stk) : Fr := (mvB true true).ren (toStk i j k)

/-- Pop one item off stack i. -/
def drp (i : Stk) : Fr := (mvB false false).ren (toStk i (other i i) (other i (other i i)))

/-! ### The loop on its four stacks -/

/-- The contents of the four stacks. -/
def st4 (A B₁ B₂ C : List Sym) : S4 → List Sym
  | .src => A
  | .t1 => B₁
  | .t2 => B₂
  | .cnt => C

section
variable (A B₁ B₂ C W : List Sym)
@[simp] theorem st4_src : st4 A B₁ B₂ C .src = A := rfl
@[simp] theorem st4_t1 : st4 A B₁ B₂ C .t1 = B₁ := rfl
@[simp] theorem st4_t2 : st4 A B₁ B₂ C .t2 = B₂ := rfl
@[simp] theorem st4_cnt : st4 A B₁ B₂ C .cnt = C := rfl
@[simp] theorem upd4_src : Function.update (st4 A B₁ B₂ C) .src W = st4 W B₁ B₂ C := by
  funext k; cases k <;> simp [Function.update, st4]
@[simp] theorem upd4_t1 : Function.update (st4 A B₁ B₂ C) .t1 W = st4 A W B₂ C := by
  funext k; cases k <;> simp [Function.update, st4]
@[simp] theorem upd4_t2 : Function.update (st4 A B₁ B₂ C) .t2 W = st4 A B₁ W C := by
  funext k; cases k <;> simp [Function.update, st4]
@[simp] theorem upd4_cnt : Function.update (st4 A B₁ B₂ C) .cnt W = st4 A B₁ B₂ W := by
  funext k; cases k <;> simp [Function.update, st4]
end

/-- The word w on top of B if p, else B. -/
def putIf (p : Bool) (w B : List Sym) : List Sym := if p then w ++ B else B

section steps
variable (p₁ p₂ : Bool) (A B₁ B₂ C : List Sym)

private theorem step_start : TM2.step (mvM p₁ p₂) ⟨some .start, none, st4 A B₁ B₂ C⟩ =
    some ⟨some .loop, none, st4 A B₁ B₂ (.L :: C)⟩ := by
  simp [TM2.step, mvM, TM2.stepAux]

private theorem step_open : TM2.step (mvM p₁ p₂) ⟨some .loop, none, st4 (.L :: A) B₁ B₂ C⟩ =
    some ⟨some .loop, none, st4 A (putIf p₁ [.R] B₁) (putIf p₂ [.R] B₂) (.R :: C)⟩ := by
  cases p₁ <;> cases p₂ <;> simp [TM2.step, mvM, pushIf, putIf, TM2.stepAux]

private theorem step_bit_in (b : Bool) : TM2.step (mvM p₁ p₂) ⟨some .loop, none, st4 (.bit b :: A) B₁ B₂ (.R :: C)⟩ =
    some ⟨some .loop, none, st4 A (putIf p₁ [.bit b] B₁) (putIf p₂ [.bit b] B₂) (.R :: C)⟩ := by
  cases p₁ <;> cases p₂ <;> simp [TM2.step, mvM, mvChk, pushIf, putIf, TM2.stepAux]

private theorem step_close_in : TM2.step (mvM p₁ p₂) ⟨some .loop, none, st4 (.R :: A) B₁ B₂ (.R :: .R :: C)⟩ =
    some ⟨some .loop, none, st4 A (putIf p₁ [.L] B₁) (putIf p₂ [.L] B₂) (.R :: C)⟩ := by
  cases p₁ <;> cases p₂ <;> simp [TM2.step, mvM, mvChk, pushIf, putIf, TM2.stepAux]

private theorem step_bit_out (b : Bool) : TM2.step (mvM p₁ p₂) ⟨some .loop, none, st4 (.bit b :: A) B₁ B₂ (.L :: C)⟩ =
    some ⟨none, none, st4 A (putIf p₁ [.bit b] B₁) (putIf p₂ [.bit b] B₂) C⟩ := by
  cases p₁ <;> cases p₂ <;> simp [TM2.step, mvM, mvChk, pushIf, putIf, TM2.stepAux]

private theorem step_close_out : TM2.step (mvM p₁ p₂) ⟨some .loop, none, st4 (.R :: A) B₁ B₂ (.R :: .L :: C)⟩ =
    some ⟨none, none, st4 A (putIf p₁ [.L] B₁) (putIf p₂ [.L] B₂) C⟩ := by
  cases p₁ <;> cases p₂ <;> simp [TM2.step, mvM, mvChk, pushIf, putIf, TM2.stepAux]

end steps

private theorem putIf_nil (p : Bool) (B : List Sym) : putIf p (mirror (code .nil)) B = putIf p [.L] (putIf p [.R] B) := by
  cases p <;> simp [putIf, code, mirror, Sym.flip]

private theorem putIf_cons (p : Bool) (x y : V) (B : List Sym) : putIf p (mirror (code (.cons x y))) B =
    putIf p [.L] (putIf p (mirror (code y)) (putIf p (mirror (code x)) (putIf p [.R] B))) := by
  cases p <;> simp [putIf, code, mirror, Sym.flip]

private theorem code_cons_append (x y : V) (A : List Sym) : code (.cons x y) ++ A = .L :: (code x ++ (code y ++ (.R :: A))) := by
  simp [code]

private theorem length_code_cons (x y : V) : (code (.cons x y)).length = 1 + (code x).length + (code y).length + 1 := by
  simp [code]; omega

/-- Inside at least one open bracket, an item is moved and the loop goes on, the count as before. -/
theorem run_inside (p₁ p₂ : Bool) : ∀ (x : V) (A B₁ B₂ C : List Sym),
    Run (TM2.step (mvM p₁ p₂)) ⟨some .loop, none, st4 (code x ++ A) B₁ B₂ (.R :: C)⟩ (code x).length
      ⟨some .loop, none, st4 A (putIf p₁ (mirror (code x)) B₁) (putIf p₂ (mirror (code x)) B₂) (.R :: C)⟩
  | .bit b, A, B₁, B₂, C => Run.one (step_bit_in p₁ p₂ A B₁ B₂ C b)
  | .nil, A, B₁, B₂, C => by
    rw [putIf_nil, putIf_nil]
    exact (Run.one (step_open p₁ p₂ (.R :: A) B₁ B₂ (.R :: C))).trans (Run.one (step_close_in p₁ p₂ A _ _ C))
  | .cons x y, A, B₁, B₂, C => by
    have h1 := Run.one (step_open p₁ p₂ (code x ++ (code y ++ (.R :: A))) B₁ B₂ (.R :: C))
    have h2 := run_inside p₁ p₂ x (code y ++ (.R :: A)) (putIf p₁ [.R] B₁) (putIf p₂ [.R] B₂) (.R :: C)
    have h3 := run_inside p₁ p₂ y (.R :: A) (putIf p₁ (mirror (code x)) (putIf p₁ [.R] B₁))
      (putIf p₂ (mirror (code x)) (putIf p₂ [.R] B₂)) (.R :: C)
    have h4 := Run.one (step_close_in p₁ p₂ A (putIf p₁ (mirror (code y)) (putIf p₁ (mirror (code x)) (putIf p₁ [.R] B₁)))
      (putIf p₂ (mirror (code y)) (putIf p₂ (mirror (code x)) (putIf p₂ [.R] B₂))) C)
    rw [code_cons_append, putIf_cons, putIf_cons, length_code_cons]
    exact ((h1.trans h2).trans h3).trans h4

/-- The loop on its four stacks: one item leaves the source and its mirror image arrives on the
chosen targets, in
|code| + 1 steps; what lies beneath is not touched. -/
theorem mvB_runs (p₁ p₂ : Bool) (x : V) (A B₁ B₂ C : List Sym) :
    (mvB p₁ p₂).Runs none (st4 (code x ++ A) B₁ B₂ C) ((code x).length + 1)
      (st4 A (putIf p₁ (mirror (code x)) B₁) (putIf p₂ (mirror (code x)) B₂) C) := by
  have h0 := Run.one (step_start p₁ p₂ (code x ++ A) B₁ B₂ C)
  have key : Run (TM2.step (mvM p₁ p₂)) ⟨some .loop, none, st4 (code x ++ A) B₁ B₂ (.L :: C)⟩ (code x).length
      ⟨none, none, st4 A (putIf p₁ (mirror (code x)) B₁) (putIf p₂ (mirror (code x)) B₂) C⟩ := by
    cases x with
    | bit b => exact Run.one (step_bit_out p₁ p₂ A B₁ B₂ C b)
    | nil =>
      rw [putIf_nil, putIf_nil]
      exact (Run.one (step_open p₁ p₂ (.R :: A) B₁ B₂ (.L :: C))).trans (Run.one (step_close_out p₁ p₂ A _ _ C))
    | cons x y =>
      have h1 := Run.one (step_open p₁ p₂ (code x ++ (code y ++ (.R :: A))) B₁ B₂ (.L :: C))
      have h2 := run_inside p₁ p₂ x (code y ++ (.R :: A)) (putIf p₁ [.R] B₁) (putIf p₂ [.R] B₂) (.L :: C)
      have h3 := run_inside p₁ p₂ y (.R :: A) (putIf p₁ (mirror (code x)) (putIf p₁ [.R] B₁))
        (putIf p₂ (mirror (code x)) (putIf p₂ [.R] B₂)) (.L :: C)
      have h4 := Run.one (step_close_out p₁ p₂ A
        (putIf p₁ (mirror (code y)) (putIf p₁ (mirror (code x)) (putIf p₁ [.R] B₁)))
        (putIf p₂ (mirror (code y)) (putIf p₂ (mirror (code x)) (putIf p₂ [.R] B₂))) C)
      rw [code_cons_append, putIf_cons, putIf_cons, length_code_cons]
      exact ((h1.trans h2).trans h3).trans h4
  have h := h0.trans key
  rw [Nat.add_comm] at h
  exact h

/-! ### The loop on the work stacks -/

theorem toStk_injective {i j k : Stk} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hi : i ≠ .cnt) (hj : j ≠ .cnt)
    (hk : k ≠ .cnt) : Function.Injective (toStk i j k) := by
  intro a b h
  cases a <;> cases b <;>
    first
    | rfl
    | (simp only [toStk] at h
       first
       | exact absurd h (by assumption)
       | exact absurd h.symm (by assumption))

/-- The loop on the work stacks: source i, targets j and k, all different, and the counter. -/
theorem mvB_ren_runs (p₁ p₂ : Bool) {i j k : Stk} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hi : i ≠ .cnt)
    (hj : j ≠ .cnt) (hk : k ≠ .cnt) (x : V) {S : Stk → List Sym} {W : List Sym} (h : S i = code x ++ W) :
    ((mvB p₁ p₂).ren (toStk i j k)).Runs none S ((code x).length + 1)
      (Function.update (Function.update (Function.update S i W) j (putIf p₁ (mirror (code x)) (S j))) k
        (putIf p₂ (mirror (code x)) (S k))) := by
  refine Frag.ren_runs (toStk i j k) (toStk_injective hij hik hjk hi hj hk)
    (mvB_runs p₁ p₂ x W (S j) (S k) (S .cnt)) ?_ ?_ ?_
  · intro q
    cases q <;> simp [toStk, h]
  · intro q
    cases q <;> simp [toStk, hij, hik, hjk, hi.symm, hj.symm, hk.symm]
  · intro q hq
    have h1 : q ≠ i := fun e => hq .src e.symm
    have h2 : q ≠ j := fun e => hq .t1 e.symm
    have h3 : q ≠ k := fun e => hq .t2 e.symm
    simp [h1, h2, h3]

theorem other_ne (i j : Stk) : other i j ≠ i ∧ other i j ≠ j ∧ other i j ≠ .cnt := by
  cases i <;> cases j <;> simp [other]

/-- `mv i j` takes the item x off stack i and puts its mirror image on stack j, in |code x| + 1
steps; nothing else
changes. -/
theorem mv_runs {i j : Stk} (hij : i ≠ j) (hi : i ≠ .cnt) (hj : j ≠ .cnt) (x : V) {S : Stk → List Sym} {W : List Sym}
    (h : S i = code x ++ W) :
    (mv i j).Runs none S ((code x).length + 1) (Function.update (Function.update S i W) j (mirror (code x) ++ S j)) := by
  obtain ⟨h1, h2, h3⟩ := other_ne i j
  have r := mvB_ren_runs true false hij h1.symm h2.symm hi hj h3 x h
  have e : Function.update (Function.update (Function.update S i W) j (putIf true (mirror (code x)) (S j))) (other i j)
      (putIf false (mirror (code x)) (S (other i j))) =
      Function.update (Function.update S i W) j (mirror (code x) ++ S j) := by
    funext q
    by_cases hq : q = other i j
    · subst hq; simp [putIf, h1, h2]
    · simp [Function.update_apply, putIf, hq]
  rw [e] at r
  exact r

/-- The way back: a mirrored item becomes the item. -/
theorem mv_runs' {i j : Stk} (hij : i ≠ j) (hi : i ≠ .cnt) (hj : j ≠ .cnt) (x : V) {S : Stk → List Sym} {W : List Sym}
    (h : S i = mirror (code x) ++ W) :
    (mv i j).Runs none S ((code x).length + 1) (Function.update (Function.update S i W) j (code x ++ S j)) := by
  have r := mv_runs hij hi hj x.mir (S := S) (W := W) (by rw [code_mir]; exact h)
  rw [code_mir, mirror_mirror, length_mirror] at r
  exact r

/-- `mv2 i j k` takes the item x off stack i and puts its mirror image on both stacks j and k, in |code
x| + 1 steps. -/
theorem mv2_runs {i j k : Stk} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (hi : i ≠ .cnt) (hj : j ≠ .cnt) (hk : k ≠ .cnt)
    (x : V) {S : Stk → List Sym} {W : List Sym} (h : S i = code x ++ W) :
    (mv2 i j k).Runs none S ((code x).length + 1)
      (Function.update (Function.update (Function.update S i W) j (mirror (code x) ++ S j)) k (mirror (code x) ++ S k)) :=
  mvB_ren_runs true true hij hik hjk hi hj hk x h

/-- `drp i` removes the item x from stack i in |code x| + 1 steps; nothing else changes. -/
theorem drp_runs {i : Stk} (hi : i ≠ .cnt) (x : V) {S : Stk → List Sym} {W : List Sym} (h : S i = code x ++ W) :
    (drp i).Runs none S ((code x).length + 1) (Function.update S i W) := by
  obtain ⟨h1, -, h3⟩ := other_ne i i
  obtain ⟨k1, k2, k3⟩ := other_ne i (other i i)
  have r := mvB_ren_runs false false h1.symm k1.symm k2.symm hi h3 k3 x h
  have e : Function.update (Function.update (Function.update S i W) (other i i)
      (putIf false (mirror (code x)) (S (other i i)))) (other i (other i i))
      (putIf false (mirror (code x)) (S (other i (other i i)))) = Function.update S i W := by
    funext q
    by_cases hq : q = other i (other i i)
    · subst hq; simp [putIf, k1]
    · by_cases hq' : q = other i i
      · subst hq'; simp [putIf, h1, hq]
      · simp [Function.update_apply, putIf, hq, hq']
  rw [e] at r
  exact r

end Groundwork.TM
