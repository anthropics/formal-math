/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSatStatement
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! From «`InTimeTM δ` for every δ > 0» (3-SAT in time O(2^{δn}) on Turing machines) to ¬ ETH_TM and
back (`not_ETH_TM_iff`):
the set of δ with `InTimeTM δ` is upward closed (`InTimeTM.mono`), so its infimum is 0 exactly if it
contains every δ > 0. -/

namespace Sat3

open Turing
open scoped NNReal ENNReal

/-- A machine that decides within t decides within any larger bound. -/
public theorem DecidesTM.mono {M : TM2ComputableAux Bool Bool} {t t' : ℕ → ℕ} (h : DecidesTM M t)
    (ht : ∀ n, t n ≤ t' n) : DecidesTM M t' := by
  intro n φ hφ
  obtain ⟨b, hb, ⟨ev⟩⟩ := h n φ hφ
  exact ⟨b, hb, ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans (ht n)⟩⟩⟩

/-- More time is allowed for a larger δ. -/
public theorem InTimeTM.mono {δ δ' : ℝ≥0} (h : InTimeTM δ) (hδ : δ ≤ δ') : InTimeTM δ' := by
  obtain ⟨M, c, hfin, hM⟩ := h
  refine ⟨M, c, hfin, hM.mono fun n => Nat.floor_le_floor ?_⟩
  have : (2 : ℝ) ^ ((δ : ℝ) * n) ≤ (2 : ℝ) ^ ((δ' : ℝ) * n) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg n))
  exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg c)

/-- The negation of ETH_TM is «on Turing machines 3-SAT is in time O(2^{δn}) for every δ > 0». -/
public theorem not_ETH_TM_iff : ¬ETH_TM ↔ ∀ δ : ℝ≥0, 0 < δ → InTimeTM δ := by
  refine ⟨fun h δ hδ => ?_, fun h hpos => ?_⟩
  · have hlt : s₃TM < δ := (not_lt.1 h).trans_lt (ENNReal.coe_pos.2 hδ)
    simp only [s₃TM, iInf_lt_iff] at hlt
    obtain ⟨δ₀, h₀, hlt⟩ := hlt
    exact h₀.mono (ENNReal.coe_le_coe.1 hlt.le)
  · obtain ⟨r, hr₀, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hpos
    exact (show s₃TM ≤ r from iInf₂_le r (h r (ENNReal.coe_pos.1 hr₀))).not_gt hr

end Sat3
