/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ClausesOccurStatement
import OccurM.ArithBack
import VariableBound.Paper.Rename.Math
import ClauseBound.Alg.End

/-! # Back to the formulas in which every variable occurs

Let M count as in `ClausesOccur.CountsUnaryFor α`, on the code with N in unary. If all n variables
of φ occur then n is the number of variables that occur and the two ways of counting agree
(`VariableBound.Rename.allOccurStmt`), n ≤ k·m
(`ClauseBound.Alg.End.n_le`), and the code has at most 8·(k·m)² bits
(`ClauseBound.Alg.End.length_enc_succ_le`); so the polynomial in the length of the formula is
absorbed (`OccurM.back_le`). The machine is the same. -/

public section

namespace ClausesOccur

open Turing MainTheoremForms
open Sat3 (CNF)

/-- What a machine that counts as in `ClausesOccur.CountsUnaryFor α`, on the code with N in unary,
gives for the formulas in which every variable occurs, for the same machine: the body of
`SatM.CountInRate` for m ≥ 2, with the constant 650·C + 1. -/
theorem allOccurOfUnary : AllOccurOfUnaryStmt := by
  intro α h0 h1 M C hM
  refine ⟨650 * C + 1, fun k n φ hk hm hφ ho => ?_⟩
  obtain ⟨e1, e2⟩ := VariableBound.Rename.allOccurStmt n φ ho
  have h := hM k n φ hk hφ hm
  unfold CountsOccWithin at h
  rw [e1, e2] at h
  obtain ⟨ev⟩ := h
  have hl := ClauseBound.Alg.End.length_enc_succ_le hk (by omega) (ClauseBound.Alg.End.n_le hφ ho)
  exact ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans (OccurM.back_le h0 h1 C hk hm (by omega))⟩⟩

end ClausesOccur
