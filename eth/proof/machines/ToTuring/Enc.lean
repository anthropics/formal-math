/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.TM.Tree
public import StepMachines.Prog.Stepped
public import Mathlib.Data.Nat.Bits
public import Mathlib.Data.Nat.Size

/-! How the data of the algorithm are written as trees, hence as words on a stack. There is no
decoding: the machines are only
ever asked to turn the word of a value into the word of another value. -/

@[expose] public section

namespace Groundwork

open TM

/-- Data as trees. -/
class Enc (α : Type) where
  /-- the tree of a value -/
  toV : α → V

open Enc

instance : Enc Unit := ⟨fun _ => .nil⟩
instance : Enc Bool := ⟨.bit⟩
instance {α β : Type} [Enc α] [Enc β] : Enc (α × β) := ⟨fun p => .cons (toV p.1) (toV p.2)⟩
instance {α : Type} [Enc α] : Enc (List α) := ⟨fun l => l.foldr (fun x v => .cons (toV x) v) .nil⟩
instance {α : Type} [Enc α] : Enc (Option α) := ⟨fun o => o.elim .nil fun x => .cons (toV x) .nil⟩
instance {α β : Type} [Enc α] [Enc β] : Enc (α ⊕ β) :=
  ⟨fun s => s.elim (fun x => .cons (.bit false) (toV x)) fun y => .cons (.bit true) (toV y)⟩
/-- A number is the list of its binary digits, lowest first, no leading zero; 0 is the empty list. -/
instance : Enc ℕ := ⟨fun n => toV (Nat.bits n)⟩
/-- An integer is «negative?» and its absolute value. -/
instance : Enc ℤ := ⟨fun z => toV (decide (z < 0), z.natAbs)⟩

/-- The word that stands for x on a stack. -/
def wd {α : Type} [Enc α] (x : α) : List Sym := code (toV x)

/-- The length of the word of x. -/
def len {α : Type} [Enc α] (x : α) : ℕ := (wd x).length

/-- The word of a value is at most linear in its size (`HasSize`, the measure in which the states of
the algorithm are bounded):
len x + 2 ≤ 7·size x. -/
class Carried (α : Type) [Enc α] [HasSize α] : Prop where
  le : ∀ x : α, len x + 2 ≤ 7 * size x

end Groundwork
