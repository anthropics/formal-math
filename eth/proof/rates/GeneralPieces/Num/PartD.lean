/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSatRateStatement
public import PaddedDescent.RateLemmas
public import PaddedDescent.Main
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Part (d) of Theorem A

Part (d) says: one deterministic algorithm decides 3-SAT on n variables in time 2^{O(n/(log
n)^{α'/10})}, α' = log(1/ρ). Here it follows from a stronger theorem of this development, 3-SAT in
time
2^{O(n/(log n)^{3/19})} on one Turing machine, because α'/10 ≤ 1/10 ≤ 3/19. So it holds without any
pieces, and the route of the paper's proof (a sparsification that takes ε as an input, then part (c)
on every formula that it produces) is not followed. Besides part (d), the file proves 0 ≤ α' ≤ 1 for
1/2 ≤ ρ < 1, which gives α'/10 ≤ 1/10. -/

@[expose] public section

namespace GeneralPieces.PartD

/-- 0 ≤ α' ≤ 1 for 1/2 ≤ ρ < 1, where α' = log(1/ρ). -/
theorem alpha_mem (ρ : ℝ) (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) : 0 ≤ Real.logb 2 (1 / ρ) ∧ Real.logb 2 (1 / ρ) ≤ 1 := by
  have hρ0 : 0 < ρ := by linarith
  constructor
  · exact Real.logb_nonneg (by norm_num) (by rw [le_div_iff₀ hρ0]; linarith)
  · rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity), Real.rpow_one, div_le_iff₀ hρ0]
    linarith

/-- Part (d): one Turing machine decides 3-SAT on n variables within C·2^{C·n/(log₂(n+2))^{α'/10}}
steps. It is a consequence of the bound with the exponent 3/19, which is proved in this development
by another route and needs no pieces. -/
theorem thmRunningTime_d (ρ : ℝ) (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) : Sat3.InRateTM (Real.logb 2 (1 / ρ) / 10) :=
  Sat3.inRateTM.mono (by linarith [(alpha_mem ρ hρ hρ1).2])

end GeneralPieces.PartD
