/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.ThmD.UnionDecimal

/-!
# Certified decimal form of the Montgomery--Taylor critical-line endpoint

The exact endpoint is `HD 1`.  This file reuses the Taylor-remainder
certificate from `UnionDecimal.lean` to give a rational enclosure and canonical
epsilon-form count statements.  No floating-point computation enters a proof.
-/

open Filter

noncomputable section

namespace Zeta23.ThmD

/-- A kernel-checked decimal enclosure of the Montgomery--Taylor critical-line endpoint. -/
theorem HD_one_decimal :
    (672500703679 / 10 ^ 12 : ℝ) < HD 1 ∧
      HD 1 < (6725007036796 / 10 ^ 13 : ℝ) := by
  have h := collisionEndpoint_decimal
  have hrel :
      1 - ((cStar 1)⁻¹ - 1) / 3 = (2 + HD 1) / 3 := by
    unfold HD
    rw [one_div]
    ring
  rw [hrel] at h
  constructor <;> linarith

/-- In particular, the exact endpoint is strictly greater than `67.2%`. -/
theorem HD_one_gt_672 :
    (672 / 10 ^ 3 : ℝ) < HD 1 := by
  exact (by norm_num : (672 / 10 ^ 3 : ℝ) <
    672500703679 / 10 ^ 12).trans HD_one_decimal.1

/-- The exact endpoint is also strictly greater than `67.25%`. -/
theorem HD_one_gt_6725 :
    (6725 / 10 ^ 4 : ℝ) < HD 1 := by
  exact (by norm_num : (6725 / 10 ^ 4 : ℝ) <
    672500703679 / 10 ^ 12).trans HD_one_decimal.1

/-- Certified decimal lower endpoint for distinct on-line zeros in dyadic windows. -/
theorem thmD₀_decimal :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((672500703679 / 10 ^ 12 : ℝ) - ε) *
          (Ncount T (2 * T) : ℝ) ≤
        N0star T (2 * T) := by
  intro ε hε
  have hη : 0 < HD 1 - (672500703679 / 10 ^ 12 : ℝ) + ε := by
    linarith [HD_one_decimal.1]
  obtain ⟨T₀, hT₀⟩ := thmD₀
    (HD 1 - (672500703679 / 10 ^ 12 : ℝ) + ε) hη
  refine ⟨T₀, fun T hT => ?_⟩
  convert hT₀ T hT using 1
  ring

/-- Certified decimal lower endpoint for distinct on-line zeros in cumulative windows. -/
theorem thmD₀_cumulative_decimal :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((672500703679 / 10 ^ 12 : ℝ) - ε) * (Ncount 0 T : ℝ) ≤
        N0star 0 T := by
  intro ε hε
  have hη : 0 < HD 1 - (672500703679 / 10 ^ 12 : ℝ) + ε := by
    linarith [HD_one_decimal.1]
  obtain ⟨T₀, hT₀⟩ := thmD₀_cumulative
    (HD 1 - (672500703679 / 10 ^ 12 : ℝ) + ε) hη
  refine ⟨T₀, fun T hT => ?_⟩
  convert hT₀ T hT using 1
  ring

/-- Certified decimal lower endpoint for simple on-line zeros in dyadic windows. -/
theorem thmD₀_simple_mult_decimal :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((672500703679 / 10 ^ 12 : ℝ) - ε) *
          (Ncount T (2 * T) : ℝ) ≤
        N0simple T (2 * T) := by
  intro ε hε
  have hη : 0 < HD 1 - (672500703679 / 10 ^ 12 : ℝ) + ε := by
    linarith [HD_one_decimal.1]
  obtain ⟨T₀, hT₀⟩ := thmD₀_simple_mult
    (HD 1 - (672500703679 / 10 ^ 12 : ℝ) + ε) hη
  refine ⟨T₀, fun T hT => ?_⟩
  convert hT₀ T hT using 1
  ring

/-- Certified decimal lower endpoint for simple on-line zeros in cumulative windows. -/
theorem thmD₀_simple_mult_cumulative_decimal :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((672500703679 / 10 ^ 12 : ℝ) - ε) * (Ncount 0 T : ℝ) ≤
        N0simple 0 T := by
  intro ε hε
  have hη : 0 < HD 1 - (672500703679 / 10 ^ 12 : ℝ) + ε := by
    linarith [HD_one_decimal.1]
  obtain ⟨T₀, hT₀⟩ := thmD₀_simple_mult_cumulative
    (HD 1 - (672500703679 / 10 ^ 12 : ℝ) + ε) hη
  refine ⟨T₀, fun T hT => ?_⟩
  convert hT₀ T hT using 1
  ring

private theorem fixed_lower_of_eps_form {c q : ℝ} {N lower : ℝ → ℝ}
    (hq : q < c)
    (h : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (c - ε) * N T ≤ lower T) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, q * N T ≤ lower T := by
  obtain ⟨T₀, hT₀⟩ := h (c - q) (sub_pos.mpr hq)
  refine ⟨T₀, fun T hT => ?_⟩
  convert hT₀ T hT using 1
  ring

/-- A fixed-coefficient headline: eventually at least `67.25%` of all
multiplicity units are represented by distinct on-line zeros. -/
theorem thmD₀_6725 :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (6725 / 10 ^ 4 : ℝ) * (Ncount T (2 * T) : ℝ) ≤
        N0star T (2 * T) :=
  fixed_lower_of_eps_form HD_one_gt_6725 thmD₀

/-- Cumulative fixed-coefficient `67.25%` critical-line headline. -/
theorem thmD₀_cumulative_6725 :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (6725 / 10 ^ 4 : ℝ) * (Ncount 0 T : ℝ) ≤ N0star 0 T :=
  fixed_lower_of_eps_form HD_one_gt_6725 thmD₀_cumulative

/-- Stronger fixed-coefficient headline: eventually at least `67.25%` of all
multiplicity units are represented by simple on-line zeros. -/
theorem thmD₀_simple_mult_6725 :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (6725 / 10 ^ 4 : ℝ) * (Ncount T (2 * T) : ℝ) ≤
        N0simple T (2 * T) :=
  fixed_lower_of_eps_form HD_one_gt_6725 thmD₀_simple_mult

/-- Cumulative fixed-coefficient `67.25%` simple-and-on-line headline. -/
theorem thmD₀_simple_mult_cumulative_6725 :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (6725 / 10 ^ 4 : ℝ) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  fixed_lower_of_eps_form HD_one_gt_6725 thmD₀_simple_mult_cumulative

end Zeta23.ThmD
