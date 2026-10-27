/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import KSatStatement
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! A consequence of «`InTimeTM k δ` for every δ > 0», that is, of «k-SAT is in time O(2^{δn}) for
every δ > 0»: the infimum `sTM k` (the s_k of Definition 6) is 0. -/

namespace SatK

open scoped NNReal ENNReal

/-- If k-SAT is in time O(2^{δn}) for every δ > 0, then s_k = 0. -/
public theorem sTM_eq_zero_of {k : ℕ} (h : ∀ δ : ℝ≥0, 0 < δ → InTimeTM k δ) : sTM k = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
  rw [zero_add]
  exact iInf₂_le ε (h ε hε)

end SatK
