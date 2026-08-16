/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Challenge/Union.lean — TRUSTED comparator challenge module: the beyond-paper
Montgomery--Taylor endpoint for zeros that are simple or on the critical line.

`Ncount` counts every zero with multiplicity.  The right side is the direct
inclusion--exclusion union count `N0 + Nsimple - N0simple`: on-line zeros are
counted with multiplicity, and simple off-line zeros once.  The exact proportion
is `1 - (cMT⁻¹ - 1) / (3/2 + √2)`.  The decimal corollaries use the
kernel-certified strict lower bound `0.887620008173`.  All vocabulary is defined
from Mathlib alone in ChallengeDeps.lean.  Proof: Solution.Union.  Config: comparator/config-union.json.

The four `sorry`s are deliberate (challenge side).
-/
import ChallengeDeps

noncomputable section

/-- At least `1 - (c₁*⁻¹ - 1)/(3/2 + √2)` of the nontrivial zeros of ζ are
simple or on the critical line (dyadic windows), with multiplicity and
inclusion--exclusion as described above. -/
theorem montgomery_taylor_simple_or_on_critical_line_union :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1 - (cMT⁻¹ - 1) / (3 / 2 + Real.sqrt 2) - ε) *
          (Ncount T (2 * T) : ℝ) ≤
        ((N0 T (2 * T) + Nsimple T (2 * T) - N0simple T (2 * T) : ℕ) : ℝ) := by
  sorry

/-- The same exact endpoint in cumulative windows `0 < Im ρ ≤ T`. -/
theorem montgomery_taylor_simple_or_on_critical_line_union_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1 - (cMT⁻¹ - 1) / (3 / 2 + Real.sqrt 2) - ε) *
          (Ncount 0 T : ℝ) ≤
        ((N0 0 T + Nsimple 0 T - N0simple 0 T : ℕ) : ℝ) := by
  sorry

/-- The certified decimal lower endpoint in dyadic windows. -/
theorem montgomery_taylor_simple_or_on_critical_line_union_decimal :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((887620008173 / 10 ^ 12 : ℝ) - ε) *
          (Ncount T (2 * T) : ℝ) ≤
        ((N0 T (2 * T) + Nsimple T (2 * T) - N0simple T (2 * T) : ℕ) : ℝ) := by
  sorry

/-- The certified decimal lower endpoint in cumulative windows. -/
theorem montgomery_taylor_simple_or_on_critical_line_union_cumulative_decimal :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((887620008173 / 10 ^ 12 : ℝ) - ε) * (Ncount 0 T : ℝ) ≤
        ((N0 0 T + Nsimple 0 T - N0simple 0 T : ℕ) : ℝ) := by
  sorry
