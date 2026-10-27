/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GraphProblems.Interfaces
public import GraphProblems.Host
public import GraphProblems.Engine
public import GraphProblems.Sized
public import GraphProblems.SetTM
import Mathlib.Tactic

/-! # The reader for the proper colorings (Corollary 7)

`readC k` applies `read1` to its input, giving a length n and a second part, and returns n·k in
unary together with the formula `colorF k n` of that second part on n·k variables,
without repeated clauses. `readC_aux` and `readC_polyT`: this reader runs in polynomial time. -/

namespace GraphProblems

open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat Turing

/-- The reader: (n·k in unary, formula). -/
@[expose] public def readC (k : ℕ) (x : List Bool) : List Unit × Fml :=
  (List.replicate ((read1 x).1.length * k) (), (colorF k (read1 x).1.length (read1 x).2).dedup)

theorem readC_aux (k : ℕ) {r : List Bool → List Unit × List Bool} (hr : PolyT r)
    (hF : PolyT fun a : List Unit × List Bool => colorF k a.1.length a.2) :
    PolyT fun x => (List.replicate ((r x).1.length * k) (), (colorF k (r x).1.length (r x).2).dedup) := by
  have h1 : PolyT fun x : List Bool => List.replicate ((r x).1.length * k) () :=
    (Unary.of_length (w := fun x => (r x).1) (by fun_prop)).mul (Unary.const k)
  have h3 : PolyT fun x : List Bool => colorF k (r x).1.length (r x).2 := PolyT.comp hF hr
  exact PolyT.prodMk h1 (PolyT.dedup h3)

public theorem readC_polyT (hR : StCertRead) (hF : StCertForm) (k : ℕ) : PolyT (readC k) := readC_aux k hR.1 (hF.2.2.2 k)

end GraphProblems
