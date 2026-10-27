/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsificationLemma.Cal.Defs

/-! # Definitions for Step 5 of Appendix D and for Appendix C

The list of all nodes of the tree of a step function (`nodesOf`), the number Δ of an output
(`StepSparsify.DeltaOf`) and the largest number of literals in a clause (`StepSparsify.widthOf`).
This file has definitions only. The theorems are in
proof/sparsification/SparsificationLemma/Nodes.lean,
proof/sparsification/SparsificationLemma/StepSparsify.lean and
proof/sparsification/SparsificationLemma/Sketch.lean. -/

@[expose] public section

namespace SparsificationLemma

open Finset Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat

/-- All nodes of the tree below s, with paths cut after d steps: s, then the nodes below its first
child, then those below its second child. -/
def nodesOf {σ : Type} (step : σ → Option (σ × σ)) : ℕ → σ → List σ
  | 0, s => [s]
  | d + 1, s =>
    match step s with
    | none => [s]
    | some (l, h) => s :: (nodesOf step d l ++ nodesOf step d h)

namespace StepSparsify

open SparsificationLemma.Cal

/-- Δ of a formula Φ on the variables below n: the larger of 2 and the largest number of clauses of
Φ in which one variable v < n occurs («Δ the larger of 2 and the largest number of its clauses in
which one variable occurs»). -/
def DeltaOf (n : ℕ) (Φ : PFml) : ℕ := max 2 ((range n).sup fun v => occN Φ v)

/-- The largest number of literals in a clause of φ, and 0 if φ has no clause («the largest number
of literals in a clause of its input»). -/
def widthOf (φ : PFml) : ℕ := φ.foldr (fun C m => max C.length m) 0

end StepSparsify

end SparsificationLemma
