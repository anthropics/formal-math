/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.Poly.Words
public import ToTuring.Lib.List3
public import StepMachines.Prog.Decode

/-! `dec` of StepMachines/Prog/Decode.lean, which reads a formula from the input word, is
polynomial-time. -/

@[expose] public section

namespace Groundwork.Decode

variable {α : Type} [Enc α]

@[fun_prop] theorem width_polyT {n : α → ℕ} (hn : PolyT n) : PolyT fun x => width (n x) := by
  unfold width; fun_prop

@[fun_prop] theorem slotDec_polyT {v : α → ℕ} (hv : PolyT v) : PolyT fun x => slotDec (v x) := by
  unfold slotDec; fun_prop

@[fun_prop] theorem clauseDec_polyT {w : α → ℕ} {b : α → List Bool} (hw : PolyT w) (hb : PolyT b) :
    PolyT fun x => clauseDec (w x) (b x) := by
  unfold clauseDec; fun_prop

/-- Reading the list of clauses from the body b of the input, one block of 3·w bits per clause, is
polynomial-time. This is the
second component of `dec`. -/
theorem clauses_polyT {w : α → ℕ} {b : α → List Bool} (hw : PolyT w) (hb : PolyT b) :
    PolyT fun x => ((List.range (b x).length).take ((b x).length / (3 * w x))).map fun c =>
      clauseDec (w x) (block (3 * w x) c (b x)) := by
  have hr : PolyT fun x => List.range (b x).length := PolyT.range (Unary.of_length hb)
  have ht : PolyT fun x => (List.range (b x).length).take ((b x).length / (3 * w x)) :=
    PolyT.take (by fun_prop) hr
  exact PolyT.map (f := fun x c => clauseDec (w x) (block (3 * w x) c (b x))) (by fun_prop) ht

/-- The decoder dec, which reads the input of the algorithm, is polynomial-time. -/
theorem dec_polyT : PolyT dec := by
  have hn : PolyT fun x : List Bool => (x.takeWhile id).length := by fun_prop
  have hb : PolyT fun x : List Bool => (x.dropWhile id).tail := by fun_prop
  exact PolyT.prodMk hn (clauses_polyT (width_polyT hn) hb)

end Groundwork.Decode
