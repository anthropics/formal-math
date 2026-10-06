/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Lang.Syntax
public import ThreeSumApsp.Util.List
public import Mathlib.Tactic.SplitIfs

/-!
# Runs stay within their limits

Facts about the semantics of the light language; none of them mentions the compiler.  A state is
bounded if every variable and every cell holds a number of absolute value at most `lim.word`.

* The value of a safe expression in a bounded state is such a number (`Expr.abs_val_le`).
* A run that starts in a bounded state ends in one (`Exec.bounded`): induction on the run.  An
  assignment and a store write the value of a safe expression; a call starts in a frame that holds
  the values of safe expressions and zeros (`bounded_callFrame`, a case of `bounded_frame`).
* A run does not change the cells from `lim.space` on (`Exec.mem_outside`).

The compiler's proof needs the first two because a word of the machine stands for a number only as
long as the number is in the range of words, and the third because its end theorem speaks of all
cells of the memory, also of those that the run may not touch.
-/

public section

namespace Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-- Writing a bounded number into a bounded function. -/
private theorem abs_update_le {f : ℕ → ℤ} {B v : ℤ} (hf : ∀ y, |f y| ≤ B) (hv : |v| ≤ B)
    (x y : ℕ) : |Function.update f x v y| ≤ B := by
  rw [Function.update_apply]
  split_ifs
  exacts [hv, hf y]

/-- The value of a safe expression in a bounded state fits in a word. -/
theorem Expr.abs_val_le {σ : State} (hσ : σ.Bounded lim) :
    ∀ e : Expr, e.Safe lim σ → |e.val σ| ≤ lim.word
  | .const n, h => by
    rw [Expr.val, abs_of_nonneg (Int.natCast_nonneg n)]
    exact h
  | .var x, _ => hσ.1 x
  | .op _ _ _, h => h.2.2
  | .load _, _ => hσ.2 _

/-- A frame that holds words, over a memory that holds words, is a bounded state. -/
theorem bounded_frame {args : List ℤ} {μ : ℕ → ℤ} (hargs : ∀ v ∈ args, |v| ≤ lim.word)
    (hμ : ∀ a, |μ a| ≤ lim.word) : State.Bounded lim ⟨frame args, μ⟩ :=
  ⟨ThreeSumApsp.AbsLe.abs_getD_le ((abs_nonneg _).trans (hμ 0)) hargs, hμ⟩

/-- The state in which a procedure starts is bounded, if the state of the caller is bounded and the
arguments of the call are safe. -/
theorem bounded_callFrame {σ : State} (hσ : σ.Bounded lim) (args : List Expr)
    (ha : ∀ e ∈ args, e.Safe lim σ) : State.Bounded lim ⟨frame (args.map (·.val σ)), σ.mem⟩ := by
  refine bounded_frame (fun v hv => ?_) hσ.2
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hv
  exact Expr.abs_val_le hσ e (ha e he)

/-- A run that starts with words in all variables and cells ends with words in all of them. -/
theorem Exec.bounded {s : Stmt} {σ σ' : State} {c : ℕ} (h : Exec lim P d s σ σ' c)
    (hσ : σ.Bounded lim) : σ'.Bounded lim := by
  induction h with
  | skip => exact hσ
  | set hs => exact ⟨abs_update_le hσ.1 (Expr.abs_val_le hσ _ hs) _, hσ.2⟩
  | store _ he _ => exact ⟨hσ.1, abs_update_le hσ.2 (Expr.abs_val_le hσ _ he) _⟩
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ hσ)
  | iteTrue _ _ _ ih => exact ih hσ
  | iteFalse _ _ _ ih => exact ih hσ
  | whileFalse _ _ => exact hσ
  | whileTrue _ _ _ _ ih₁ ih₂ => exact ih₂ (ih₁ hσ)
  | call ha _ _ _ ih =>
    have hbody := ih (bounded_callFrame hσ _ ha)
    exact ⟨abs_update_le hσ.1 (hbody.1 0) _, hbody.2⟩

/-- A run does not change the cells from lim.space on. -/
theorem Exec.mem_outside {s : Stmt} {σ σ' : State} {c : ℕ} (h : Exec lim P d s σ σ' c) (a : ℕ)
    (ha : lim.space ≤ a) : σ'.mem a = σ.mem a := by
  induction h with
  | skip => rfl
  | set _ => rfl
  | store _ _ haddr =>
    obtain ⟨h0, hlt⟩ := haddr
    exact Function.update_of_ne (by omega) _ _
  | seq _ _ ih₁ ih₂ => rw [ih₂, ih₁]
  | iteTrue _ _ _ ih => exact ih
  | iteFalse _ _ _ ih => exact ih
  | whileFalse _ _ => rfl
  | whileTrue _ _ _ _ ih₁ ih₂ => rw [ih₂, ih₁]
  | call _ _ _ _ ih => exact ih

end Light
