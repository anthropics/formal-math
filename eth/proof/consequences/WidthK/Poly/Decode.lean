/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ToTuring.Poly.Decode
public import WidthK.Decode

/-! `decK k` of WidthK/Decode.lean, which reads a formula of width k from the input word, is
polynomial-time (`decK_polyT`). The width k is a
constant of the function, not part of its input. The file follows
proof/machines/ToTuring/Poly/Decode.lean line by line, with a parameter k for its width 3, and uses
that file's lemmas `width_polyT` and `slotDec_polyT`. -/

@[expose] public section

namespace Groundwork.DecodeK

open Groundwork.Decode

variable {α : Type} [Enc α]

/-- Reading one clause from a block of k slots of w bits is polynomial-time. -/
@[fun_prop] theorem clauseDec_polyT (k : ℕ) {w : α → ℕ} {b : α → List Bool} (hw : PolyT w) (hb : PolyT b) :
    PolyT fun x => clauseDec k (w x) (b x) := by
  unfold clauseDec; fun_prop

/-- Reading the list of clauses from the body b of the input, one block of k·w bits per clause, is
polynomial-time. This is the
second component of `decK k`. -/
theorem clauses_polyT (k : ℕ) {w : α → ℕ} {b : α → List Bool} (hw : PolyT w) (hb : PolyT b) :
    PolyT fun x => ((List.range (b x).length).take ((b x).length / (k * w x))).map fun c =>
      clauseDec k (w x) (block (k * w x) c (b x)) := by
  have hr : PolyT fun x => List.range (b x).length := PolyT.range (Unary.of_length hb)
  have ht : PolyT fun x => (List.range (b x).length).take ((b x).length / (k * w x)) :=
    PolyT.take (by fun_prop) hr
  exact PolyT.map (f := fun x c => clauseDec k (w x) (block (k * w x) c (b x))) (by fun_prop) ht

/-- The decoder `decK k`, which reads the input of the algorithm, is polynomial-time. -/
theorem decK_polyT (k : ℕ) : PolyT (decK k) := by
  have hn : PolyT fun x : List Bool => (x.takeWhile id).length := by fun_prop
  have hb : PolyT fun x : List Bool => (x.dropWhile id).tail := by fun_prop
  exact PolyT.prodMk hn (clauses_polyT k (width_polyT hn) hb)

end Groundwork.DecodeK
