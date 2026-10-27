/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.TM.Frag
public import ToTuring.TM.Tree

/-! The four work stacks of all fragments, and a normal form for their contents. -/

@[expose] public section

namespace Groundwork.TM

open Turing

/-- The work stacks: the main stack, two to park items on, and the counter of open brackets. -/
inductive Stk | main | a | b | cnt
  deriving DecidableEq

instance : Fintype Stk := ⟨{.main, .a, .b, .cnt}, fun x => by cases x <;> simp⟩

/-- Fragments over the work stacks. The local state is the symbol just popped; it is `none` between
fragments. -/
abbrev Fr := Frag (fun _ : Stk => Sym) (Option Sym)

/-- The contents of the four stacks. -/
def st (M A B N : List Sym) : Stk → List Sym
  | .main => M
  | .a => A
  | .b => B
  | .cnt => N

section
variable (M A B N W : List Sym)
@[simp] theorem st_main : st M A B N .main = M := rfl
@[simp] theorem st_a : st M A B N .a = A := rfl
@[simp] theorem st_b : st M A B N .b = B := rfl
@[simp] theorem st_cnt : st M A B N .cnt = N := rfl
@[simp] theorem upd_main : Function.update (st M A B N) .main W = st W A B N := by
  funext k; cases k <;> simp [Function.update, st]
@[simp] theorem upd_a : Function.update (st M A B N) .a W = st M W B N := by
  funext k; cases k <;> simp [Function.update, st]
@[simp] theorem upd_b : Function.update (st M A B N) .b W = st M A W N := by
  funext k; cases k <;> simp [Function.update, st]
end

end Groundwork.TM
