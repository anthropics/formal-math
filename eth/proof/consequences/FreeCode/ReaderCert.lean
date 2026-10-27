/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import FreeCode.Reader
import ToTuring.Poly.Decode
import ToTuring.Closure.Fold
import ToTuring.Lib.Unary
import Mathlib.Tactic

/-! # Definition 6 with the code that does not depend on k: the reader is polynomial time

No sentence of the paper stands behind this file. `readFree` goes once through the bits with the
step `stepR`. One step adds at most the bit it reads and regroups the lists of the state, so it
makes the word of the state longer by at most a constant (`len_stepR_le`); this is what the closure
of `PolyT` under folds asks (`PolyT.foldl_add`). `stReader` proves `FreeCode.StReader`. -/

public section

namespace FreeCode

open Groundwork Groundwork.Prog Groundwork.Decode

/-- One step of the reader makes the word of the state longer by at most 12 symbols. -/
theorem len_stepR_le (w : ℕ) (s : RState) (e : Bool) : len (stepR w s e) ≤ len s + 12 := by
  obtain ⟨a, b, cur, cl, acc⟩ := s
  cases hd : decide (cur.length + 1 = w) <;> cases a <;> cases b <;> cases e <;>
    simp only [stepR, hd, cond_true, cond_false, len_pair, len_cons, len_nil, len_bool] <;> omega

/-- One step of the reader is polynomial time, with the number of bits of a literal as a part of the
input. -/
theorem stepR_polyT : PolyT fun p : ℕ × RState × Bool => stepR p.1 p.2.1 p.2.2 := by
  unfold stepR
  fun_prop

/-- Going through all bits is polynomial time. -/
theorem scanR_polyT : PolyT scanR := by
  have h := stepR_polyT
  have hw : PolyT fun x : List Bool => width (x.takeWhile id).length := by fun_prop
  have hg : PolyT fun p : List Bool × RState × Bool => stepR (width (p.1.takeWhile id).length) p.2.1 p.2.2 :=
    PolyT.comp (g := fun p : List Bool × RState × Bool => (width (p.1.takeWhile id).length, p.2.1, p.2.2)) h (by fun_prop)
  exact PolyT.foldl_add (l := fun x : List Bool => (x.dropWhile id).tail) (a := fun _ => ((false, false, [], [], []) : RState))
    (g := fun x s e => stepR (width (x.takeWhile id).length) s e) (by fun_prop) (by fun_prop) hg
    ⟨fun _ => 12, PB.const 12, fun x c e _ => len_stepR_le _ c e⟩

/-- The reader is polynomial time. -/
theorem readFree_polyT : PolyT readFree := by
  have h := scanR_polyT
  have h1 : Unary fun x : List Bool => (x.takeWhile id).length := Unary.of_length (by fun_prop)
  have h2 : PolyT fun x : List Bool => (scanR x).2.2.2.2.reverse.map fun cl => cl.reverse.map fun cur => (slotDec (ofWord cur.reverse)).getD (0, false) := by
    fun_prop
  exact PolyT.prodMk h1 h2

/-- There is a polynomial-time reader: the statement `FreeCode.StReader`. The reader is `readFree`. -/
theorem stReader : StReader := ⟨readFree, readFree_polyT, reads_readFree⟩

end FreeCode
