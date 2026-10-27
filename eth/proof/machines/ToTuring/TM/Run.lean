/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Computability.TuringMachine.Computable

/-! Runs of exactly n steps of a partial step function, and a statement of one of Mathlib's
multi-stack machines (`Turing.TM2`)
placed in a larger machine with more labels. -/

@[expose] public section

namespace Groundwork.TM

open Turing

/-! ### Runs of exactly n steps -/

/-- n steps of f lead from a to b. -/
def Run {C : Type} (f : C → Option C) : C → ℕ → C → Prop
  | a, 0, b => a = b
  | a, n + 1, b => ∃ c, f a = some c ∧ Run f c n b

theorem Run.one {C : Type} {f : C → Option C} {a b : C} (h : f a = some b) : Run f a 1 b := ⟨b, h, rfl⟩

theorem Run.trans {C : Type} {f : C → Option C} : ∀ {m : ℕ} {a b c : C} {n : ℕ}, Run f a m b → Run f b n c → Run f a (m + n) c
  | 0, _, _, _, n, h, h' => by cases h; simpa using h'
  | m + 1, _, _, _, n, ⟨d, hd, h⟩, h' => by
    rw [Nat.add_right_comm]
    exact ⟨d, hd, h.trans h'⟩

/-- The same in Mathlib's form (`StateTransition.EvalsTo`): n iterations of `flip bind f` lead from
`some a` to `some b`. -/
theorem Run.iterate {C : Type} {f : C → Option C} : ∀ {n : ℕ} {a b : C}, Run f a n b → (flip bind f)^[n] (some a) = some b
  | 0, _, _, h => by cases h; rfl
  | n + 1, a, b, ⟨c, hc, h⟩ => by
    rw [Function.iterate_succ_apply]
    have : flip bind f (some a) = some c := hc
    rw [this]; exact h.iterate

variable {K : Type} [DecidableEq K] {Γ : K → Type} {σ : Type}

/-! ### A statement placed in a larger machine -/

section place

variable {Λ Λ' : Type} (ι : Λ → Λ') (e : Option Λ')

/-- Labels are carried along ι; where the statement would halt, the larger machine goes on at e (or
halts if e = none). -/
def place : TM2.Stmt Γ Λ σ → TM2.Stmt Γ Λ' σ
  | .push k f q => .push k f (place q)
  | .peek k f q => .peek k f (place q)
  | .pop k f q => .pop k f (place q)
  | .load f q => .load f (place q)
  | .branch p q₁ q₂ => .branch p (place q₁) (place q₂)
  | .goto l => .goto (ι ∘ l)
  | .halt => match e with
    | some e => .goto fun _ => e
    | none => .halt

/-- The same for configurations. -/
def placeCfg (c : TM2.Cfg Γ Λ σ) : TM2.Cfg Γ Λ' σ := ⟨c.l.elim e (some ∘ ι), c.var, c.stk⟩

theorem stepAux_place (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ k, List (Γ k)) :
    TM2.stepAux (place ι e q) v S = placeCfg ι e (TM2.stepAux q v S) := by
  induction q generalizing v S with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih _ _
  | branch p _ _ ih₁ ih₂ => simp only [place, TM2.stepAux, ih₁, ih₂]; cases p v <;> rfl
  | goto => rfl
  | halt => cases e <;> rfl

/-- If the larger machine M' holds the placed statements of M, every run of M is a run of M' of the
same length. -/
theorem run_place {M : Λ → TM2.Stmt Γ Λ σ} {M' : Λ' → TM2.Stmt Γ Λ' σ} (hM : ∀ l, M' (ι l) = place ι e (M l)) :
    ∀ {n : ℕ} {a b : TM2.Cfg Γ Λ σ}, Run (TM2.step M) a n b → Run (TM2.step M') (placeCfg ι e a) n (placeCfg ι e b)
  | 0, _, _, h => by cases h; exact rfl
  | n + 1, ⟨none, v, S⟩, b, ⟨c, hc, _⟩ => by simp [TM2.step] at hc
  | n + 1, ⟨some l, v, S⟩, b, ⟨c, hc, h⟩ => by
    refine ⟨placeCfg ι e c, ?_, run_place hM h⟩
    simp only [TM2.step, Option.some.injEq] at hc
    simp only [placeCfg, Option.elim, Function.comp, TM2.step, hM, stepAux_place, hc]

end place

end Groundwork.TM
