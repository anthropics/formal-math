/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import MainTheoremFormsStatement
public import UniformInK.Top.Defs
import VariableBound.Paper.Arith
import VariableBound.Paper.Rename.End
import VariableBound.Paper.Rename.Code
import VariableBound.Paper.Rename.Cert
import VariableBound.Paper.Rename.Time
import ClauseBound.MainBoth
import CountKSatRate.Pad

/-! # The number of satisfying assignments as assignments of the variables that occur: satisfiability and a bound

For a formula over x₀ … x_(N−1) in which n of these variables occur, `numSatOcc` counts the
satisfying assignments as assignments of these n variables.
A formula is satisfiable exactly if this count is not 0 (`satisfiable_iff`), and the count is below
2^(n+1) (`numSatOcc_lt`). -/

public section

namespace VariableBound.Paper

open Groundwork Turing CountKSatRate VariableBound.Rename MainTheoremForms
open Sat3 (CNF)

/-- A formula is satisfiable if and only if its number of satisfying assignments, as assignments of
the variables that occur, is not 0. -/
theorem satisfiable_iff {N : ℕ} (φ : CNF N) : Sat3.Satisfiable φ ↔ numSatOcc φ ≠ 0 := by
  have h1 : Sat3.Satisfiable φ ↔ SatK.numSat φ ≠ 0 := by
    simp [SatK.numSat, Sat3.Satisfiable, Finset.filter_eq_empty_iff]
  rw [h1, numSat_eq φ]
  simp

/-- The number of satisfying assignments, as assignments of the n variables that occur, is below
2^(n+1). -/
theorem numSatOcc_lt {N : ℕ} (φ : CNF N) : numSatOcc φ < 2 ^ (numOcc φ + 1) := by
  rw [← numSat_ren]
  have h : SatK.numSat (ren φ) ≤ 2 ^ numOcc φ := by
    refine (Finset.card_filter_le _ _).trans ?_
    simp
  exact h.trans_lt (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _))

end VariableBound.Paper
