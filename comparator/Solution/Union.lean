/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Solution/Union.lean — UNTRUSTED solution module for Challenge/Union.lean.
The exact statements delegate to `Zeta23.ThmD.thmD₀_union` and its cumulative
form; the bridge below rewrites `unionProp (cStar 1)` as the challenge's closed
Mathlib expression. The decimal statements use the kernel-certified enclosure.
-/
import ChallengeDeps
import Solution
import Zeta23.ThmD.UnionDecimal

noncomputable section

/-- The library's exact endpoint union proportion in the challenge's closed form. -/
theorem unionProp_cStar_one_eq_comparator :
    Zeta23.ThmD.unionProp (Zeta23.ThmD.cStar 1) =
      1 - (cMT⁻¹ - 1) / (3 / 2 + Real.sqrt 2) := by
  unfold Zeta23.ThmD.unionProp Zeta23.ZeroSide.unionQ
  rw [cStar_one_eq_cMT]

/-- At least `1 - (c₁*⁻¹ - 1)/(3/2 + √2)` of the nontrivial zeros of ζ are
simple or on the critical line (dyadic windows), with multiplicity and
inclusion--exclusion as described in the trusted challenge. -/
theorem montgomery_taylor_simple_or_on_critical_line_union :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1 - (cMT⁻¹ - 1) / (3 / 2 + Real.sqrt 2) - ε) *
          (Ncount T (2 * T) : ℝ) ≤
        ((N0 T (2 * T) + Nsimple T (2 * T) - N0simple T (2 * T) : ℕ) : ℝ) := by
  have h := @Zeta23.ThmD.thmD₀_union
  rw [unionProp_cStar_one_eq_comparator] at h
  exact h

/-- The same exact endpoint in cumulative windows `0 < Im ρ ≤ T`. -/
theorem montgomery_taylor_simple_or_on_critical_line_union_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1 - (cMT⁻¹ - 1) / (3 / 2 + Real.sqrt 2) - ε) *
          (Ncount 0 T : ℝ) ≤
        ((N0 0 T + Nsimple 0 T - N0simple 0 T : ℕ) : ℝ) := by
  have h := @Zeta23.ThmD.thmD₀_union_cumulative
  rw [unionProp_cStar_one_eq_comparator] at h
  exact h

/-- The certified decimal lower endpoint in dyadic windows. -/
theorem montgomery_taylor_simple_or_on_critical_line_union_decimal :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((887620008173 / 10 ^ 12 : ℝ) - ε) *
          (Ncount T (2 * T) : ℝ) ≤
        ((N0 T (2 * T) + Nsimple T (2 * T) - N0simple T (2 * T) : ℕ) : ℝ) := by
  exact @Zeta23.ThmD.thmD₀_union_decimal

/-- The certified decimal lower endpoint in cumulative windows. -/
theorem montgomery_taylor_simple_or_on_critical_line_union_cumulative_decimal :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((887620008173 / 10 ^ 12 : ℝ) - ε) * (Ncount 0 T : ℝ) ≤
        ((N0 0 T + Nsimple 0 T - N0simple 0 T : ℕ) : ℝ) := by
  exact @Zeta23.ThmD.thmD₀_union_cumulative_decimal
