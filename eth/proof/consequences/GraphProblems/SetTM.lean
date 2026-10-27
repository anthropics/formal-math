/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import GraphProblems.Interfaces
public import GraphProblems.Host
public import GraphProblems.Cert
public import ToTuring.Poly.Basic
import Mathlib.Tactic

/-! # Instances, codes and polynomial-time readers, used for Turing machines for problems on graphs

The type `Inst` of instances (a graph on n vertices and a number s ≤ n), the lengths of the codes
`codeWith G s` and `code G`, the word `nzW` of the bit «not zero», the fact that `nzW` and the
binary digits `Nat.bits` are computed in polynomial time, and the reader `readF`, which splits a
word by `read2` and applies a formula F, computed in polynomial time, to the length of the
first part and to the last part; `readF_polyT` says that `readF` is computed in polynomial time. -/

namespace GraphProblems

open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat Turing

/-- The instances: a graph on n vertices and s ≤ n. -/
public abbrev Inst : Type := (n : ℕ) × SimpleGraph (Fin n) × {s : ℕ // s ≤ n}

/-- The length of the code. -/
public theorem length_codeWith (hL : StMatrixLength) {n : ℕ} (G : SimpleGraph (Fin n)) (s : ℕ) : (codeWith G s).length = n + 1 + (s + 1 + n * n) := by
  simp only [codeWith, unary, hL n G, List.length_append, List.length_replicate, List.length_cons, List.length_nil]

public theorem length_code (hL : StMatrixLength) {n : ℕ} (G : SimpleGraph (Fin n)) : (code G).length = n + 1 + n * n := by
  simp only [code, unary, hL n G, List.length_append, List.length_replicate, List.length_cons, List.length_nil]

/-- The bit «not zero», as a word. -/
@[expose] public def nzW (v : ℕ) : List Bool := [decide (v ≠ 0)]

public theorem nzW_polyT : PolyT nzW := by unfold nzW; fun_prop

public theorem bits_polyT : PolyT Nat.bits := by fun_prop

/-- The reader for a formula F. -/
@[expose] public def readF (F : ℕ → List Bool → Fml) (x : List Bool) : List Unit × ℕ × Fml :=
  ((read2 x).1, (read2 x).2.1, F (read2 x).1.length (read2 x).2.2)

theorem readF_aux {r : List Bool → List Unit × ℕ × List Bool} (hr : PolyT r) {F : ℕ → List Bool → Fml}
    (hF : PolyT fun a : List Unit × List Bool => F a.1.length a.2) : PolyT fun x => ((r x).1, (r x).2.1, F (r x).1.length (r x).2.2) := by
  have h3 : PolyT fun x : List Bool => F (r x).1.length (r x).2.2 :=
    PolyT.comp (g := fun x : List Bool => ((r x).1, (r x).2.2)) hF (by fun_prop)
  exact PolyT.prodMk (by fun_prop) (PolyT.prodMk (by fun_prop) h3)

public theorem readF_polyT (hR : StCertRead) {F : ℕ → List Bool → Fml} (hF : PolyT fun a : List Unit × List Bool => F a.1.length a.2) :
    PolyT (readF F) := readF_aux hR.2 hF

end GraphProblems
