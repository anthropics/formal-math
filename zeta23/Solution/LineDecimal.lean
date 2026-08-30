/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Solution/LineDecimal.lean — UNTRUSTED solution module for the certified
Montgomery--Taylor critical-line decimal statements.
-/
import ChallengeDeps
import Zeta23.ThmD.LineDecimal

noncomputable section

/-- Certified critical-line endpoint in dyadic windows. -/
theorem montgomery_taylor_on_critical_line_decimal :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((672500703679 / 10 ^ 12 : ℝ) - ε) *
          (Ncount T (2 * T) : ℝ) ≤
        N0star T (2 * T) :=
  Zeta23.ThmD.thmD₀_decimal

/-- Certified critical-line endpoint in cumulative windows. -/
theorem montgomery_taylor_on_critical_line_cumulative_decimal :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((672500703679 / 10 ^ 12 : ℝ) - ε) * (Ncount 0 T : ℝ) ≤
        N0star 0 T :=
  Zeta23.ThmD.thmD₀_cumulative_decimal

/-- The stronger simple-and-on-line endpoint in dyadic windows. -/
theorem montgomery_taylor_simple_on_critical_line_decimal :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((672500703679 / 10 ^ 12 : ℝ) - ε) *
          (Ncount T (2 * T) : ℝ) ≤
        N0simple T (2 * T) :=
  Zeta23.ThmD.thmD₀_simple_mult_decimal

/-- The stronger simple-and-on-line endpoint in cumulative windows. -/
theorem montgomery_taylor_simple_on_critical_line_cumulative_decimal :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((672500703679 / 10 ^ 12 : ℝ) - ε) * (Ncount 0 T : ℝ) ≤
        N0simple 0 T :=
  Zeta23.ThmD.thmD₀_simple_mult_cumulative_decimal
