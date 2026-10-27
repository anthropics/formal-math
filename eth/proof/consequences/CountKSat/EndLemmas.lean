/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountKSatStatement
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! # From «#3-SAT is in time O(2^{δn}) for every δ > 0» to the failure of the hypothesis

Plain facts on the definitions of CountKSatStatement.lean: a time bound for a counting machine may
be enlarged (`CountsTM.mono`), and the counting hypothesis `CountETH_TM` fails
if #3-SAT is in time O(2^{δn}) for every δ > 0 (`not_CountETH_TM_of`). The paper states this failure
of #ETH in Corollary 6. -/

namespace CountKSat.EndLemmas

open Turing SatK
open scoped NNReal ENNReal

/-- A machine that counts within t steps counts within any larger bound. -/
public theorem CountsTM.mono {k : ℕ} {M : TM2ComputableAux Bool Bool} {t t' : ℕ → ℕ} (h : CountsTM k M t) (ht : ∀ n, t n ≤ t' n) :
    CountsTM k M t' := fun n φ hφ => by
  obtain ⟨e⟩ := h n φ hφ
  exact ⟨⟨e.toEvalsTo, e.steps_le_m.trans (ht n)⟩⟩

/-- The hypothesis fails if #3-SAT is in time O(2^{δn}) for every δ > 0. -/
public theorem not_CountETH_TM_of (h : ∀ δ : ℝ≥0, 0 < δ → CountInTimeTM 3 δ) : ¬ CountETH_TM := fun ⟨δ, h0, hn⟩ => hn (h δ h0)

end CountKSat.EndLemmas
