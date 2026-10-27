/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Data.List.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.Ring

/-! The universal data of the machines: binary trees whose leaves are bits or empty, written with
two brackets. A word read
from the other end, its brackets exchanged, is the code of the mirrored tree; so an item that was
moved symbol by symbol to
another stack is again an item. -/

@[expose] public section

namespace Groundwork.TM

/-- Bits and two brackets. -/
inductive Sym | bit (b : Bool) | L | R
  deriving DecidableEq

instance : Fintype Sym := ⟨{.bit false, .bit true, .L, .R}, fun x => by rcases x with (_ | _) | _ | _ <;> simp⟩

@[simp] theorem beq_RL : (Sym.R == Sym.L) = false := by decide
@[simp] theorem beq_LR : (Sym.L == Sym.R) = false := by decide
@[simp] theorem beq_bL (b : Bool) : (Sym.bit b == Sym.L) = false := by cases b <;> decide
@[simp] theorem beq_bR (b : Bool) : (Sym.bit b == Sym.R) = false := by cases b <;> decide

/-- Binary trees whose leaves are bits or empty. -/
inductive V | nil | bit (b : Bool) | cons (x y : V)

/-- The code of a tree: ⟨⟩ for nil, the bit for a bit, ⟨ code x, code y ⟩ for cons x y. -/
def code : V → List Sym
  | .nil => [.L, .R]
  | .bit b => [.bit b]
  | .cons x y => .L :: (code x ++ code y ++ [.R])

/-- The other bracket. -/
def Sym.flip : Sym → Sym
  | .L => .R
  | .R => .L
  | s => s

/-- A word read from the other end, its brackets exchanged. -/
def mirror (w : List Sym) : List Sym := (w.map Sym.flip).reverse

theorem mirror_mirror (w : List Sym) : mirror (mirror w) = w := by
  have h : ∀ s : Sym, s.flip.flip = s := fun s => by cases s <;> rfl
  simp [mirror, List.map_reverse, Function.comp_def, h]

@[simp] theorem length_mirror (w : List Sym) : (mirror w).length = w.length := by simp [mirror]

/-- The mirrored tree. -/
def V.mir : V → V
  | .nil => .nil
  | .bit b => .bit b
  | .cons x y => .cons y.mir x.mir

/-- The code of the mirrored tree is the mirrored code. -/
theorem code_mir (x : V) : code x.mir = mirror (code x) := by
  induction x with
  | nil => rfl
  | bit b => rfl
  | cons x y ihx ihy => simp [V.mir, code, ihx, ihy, mirror, Sym.flip]

end Groundwork.TM
