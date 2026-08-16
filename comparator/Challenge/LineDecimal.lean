/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Challenge/LineDecimal.lean — TRUSTED comparator challenge module for the
certified decimal Montgomery--Taylor critical-line endpoint.

The coefficient `0.672500703679` is strictly below the exact endpoint and
strictly above `0.672`.  `N0star` counts distinct on-line zeros, while
`N0simple` counts simple on-line zeros.  The denominator `Ncount` counts all
zeros with multiplicity.  Proof: Solution.LineDecimal.  Config:
comparator/config-line-decimal.json.

The four `sorry`s are deliberate (challenge side).
-/
import ChallengeDeps

noncomputable section

/-- Certified critical-line endpoint in dyadic windows. -/
theorem montgomery_taylor_on_critical_line_decimal :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((672500703679 / 10 ^ 12 : ℝ) - ε) *
          (Ncount T (2 * T) : ℝ) ≤
        N0star T (2 * T) := by
  sorry

/-- Certified critical-line endpoint in cumulative windows. -/
theorem montgomery_taylor_on_critical_line_cumulative_decimal :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((672500703679 / 10 ^ 12 : ℝ) - ε) * (Ncount 0 T : ℝ) ≤
        N0star 0 T := by
  sorry

/-- The stronger simple-and-on-line endpoint in dyadic windows. -/
theorem montgomery_taylor_simple_on_critical_line_decimal :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((672500703679 / 10 ^ 12 : ℝ) - ε) *
          (Ncount T (2 * T) : ℝ) ≤
        N0simple T (2 * T) := by
  sorry

/-- The stronger simple-and-on-line endpoint in cumulative windows. -/
theorem montgomery_taylor_simple_on_critical_line_cumulative_decimal :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((672500703679 / 10 ^ 12 : ℝ) - ε) * (Ncount 0 T : ℝ) ≤
        N0simple 0 T := by
  sorry
