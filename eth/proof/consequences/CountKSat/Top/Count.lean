/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountKSat.Interfaces
public import WidthK.Top.Sat
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import all StepMachines.Prog.Sat
import all StepMachines.Prog.Decode
import all WidthK.Top.Sat

/-! Facts for the program that counts the satisfying assignments of a k-CNF in c·2^{δn} steps
(decode the input, walk the sparsification tree depth-first, count
the satisfying assignments of every leaf, add the counts up, and write the sum as n + 1 bits): there
are at most 2ⁿ satisfying assignments, a formula with an
empty clause has none, and the output function `outW` writes the count as the n + 1 bits
`SatK.binary n v`. -/

namespace CountKSat.CountTop

open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK
open Groundwork.Sparsify (leaves)

/-! ### The number of satisfying assignments -/

/-- There are at most 2ⁿ satisfying assignments. -/
theorem numSat_le {n : ℕ} (φ : Sat3.CNF n) : SatK.numSat φ ≤ 2 ^ n := by
  refine (Finset.card_filter_le _ _).trans ?_
  simp

/-- A formula with an empty clause has no satisfying assignment. -/
theorem numSat_of_nil {n : ℕ} {φ : Sat3.CNF n} (h : [] ∈ φ) : SatK.numSat φ = 0 := by
  rw [SatK.numSat, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro a _ ha
  obtain ⟨l, hl, -⟩ := ha [] h
  simp at hl

/-- The output function `outW` of the machine writes the count v as the n + 1 bits `SatK.binary n v`
that the statement of #k-SAT asks for. -/
theorem outW_eq (n : ℕ) (ψ : Fml) (v : ℕ) : outW ((List.replicate n (), ψ), v) = SatK.binary n v := by
  simp [outW, SatK.binary, Decode.toWord_eq]

end CountKSat.CountTop
