/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.TM.Stacks

/-! The stacks of the final machine: the four work stacks and one stack of bits, for input and
output (Mathlib asks that the
alphabets of the input stack and of the output stack be in bijection with Bool). A fragment over the
work stacks runs in the
final machine and does not touch the stack of bits. -/

@[expose] public section

namespace Groundwork.TM

open Turing

/-- The alphabets of the final machine: bits on `none`, Sym on the work stacks. -/
abbrev Γio : Option Stk → Type
  | none => Bool
  | some _ => Sym

/-- A statement over the work stacks, in the final machine. -/
def liftIO {Λ σ : Type} : TM2.Stmt (fun _ : Stk => Sym) Λ σ → TM2.Stmt Γio Λ σ
  | .push k f q => .push (some k) f (liftIO q)
  | .peek k f q => .peek (some k) f (liftIO q)
  | .pop k f q => .pop (some k) f (liftIO q)
  | .load f q => .load f (liftIO q)
  | .branch p q₁ q₂ => .branch p (liftIO q₁) (liftIO q₂)
  | .goto l => .goto l
  | .halt => .halt

/-- A fragment over the work stacks, in the final machine. -/
def Frag.io (P : Fr) : Frag Γio (Option Sym) where
  Λ := P.Λ
  entry := P.entry
  m l := liftIO (P.m l)

/-- The contents of the five stacks: the bits W, and S on the work stacks. -/
def withIO (W : List Bool) (S : Stk → List Sym) : ∀ k, List (Γio k)
  | none => W
  | some k => S k

/-- Overwriting a work stack commutes with adding the stack of bits. -/
@[simp] theorem update_withIO (W : List Bool) (S : Stk → List Sym) (k : Stk) (w : List Sym) :
    Function.update (withIO W S) (some k) w = withIO W (Function.update S k w) := by
  funext k'
  rcases k' with _ | k'
  · rfl
  · by_cases h : k' = k
    · subst h; simp [withIO]
    · rw [Function.update_of_ne (by simpa using h)]; simp [withIO, Function.update_of_ne h]

/-- A configuration over the work stacks, in the final machine with the bits W. -/
def liftCfg {Λ σ : Type} (W : List Bool) (c : TM2.Cfg (fun _ : Stk => Sym) Λ σ) : TM2.Cfg Γio Λ σ := ⟨c.l, c.var, withIO W c.stk⟩

/-- A statement, lifted to the final machine, does what it does over the work stacks alone, and does
not touch the bits. -/
theorem stepAux_liftIO {Λ σ : Type} (W : List Bool) (q : TM2.Stmt (fun _ : Stk => Sym) Λ σ) (v : σ) (S : Stk → List Sym) :
    TM2.stepAux (liftIO q) v (withIO W S) = liftCfg W (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push k f q ih => simp only [liftIO, TM2.stepAux, update_withIO]; exact ih _ _
  | peek k f q ih => exact ih _ _
  | pop k f q ih => simp only [liftIO, TM2.stepAux, update_withIO]; exact ih _ _
  | load f q ih => exact ih _ _
  | branch p q₁ q₂ ih₁ ih₂ => simp only [liftIO, TM2.stepAux, ih₁, ih₂]; cases p v <;> rfl
  | goto l => rfl
  | halt => rfl

/-- Runs over the work stacks are runs of the final machine. -/
theorem run_liftIO {Λ σ : Type} (W : List Bool) {M : Λ → TM2.Stmt (fun _ : Stk => Sym) Λ σ} :
    ∀ {n : ℕ} {a b : TM2.Cfg (fun _ : Stk => Sym) Λ σ}, Run (TM2.step M) a n b →
      Run (TM2.step fun l => liftIO (M l)) (liftCfg W a) n (liftCfg W b)
  | 0, _, _, h => by cases h; exact rfl
  | n + 1, ⟨none, v, S⟩, b, ⟨c, hc, _⟩ => by simp [TM2.step] at hc
  | n + 1, ⟨some l, v, S⟩, b, ⟨c, hc, h⟩ => by
    refine ⟨liftCfg W c, ?_, run_liftIO W h⟩
    simp only [TM2.step, Option.some.injEq] at hc
    simp only [liftCfg, TM2.step, stepAux_liftIO, hc]

/-- A run of a fragment over the work stacks is a run of the same length of `P.io`, and leaves the
bits W as they were. -/
theorem Frag.io_runs {P : Fr} {v : Option Sym} {S S' : Stk → List Sym} {n : ℕ} (h : P.Runs v S n S') (W : List Bool) :
    P.io.Runs v (withIO W S) n (withIO W S') :=
  run_liftIO W h

end Groundwork.TM
