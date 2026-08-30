/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Solution/SextupleA1285.lean — UNTRUSTED solution module for the refined
(`A = 257 / 20000`) sextuple simple-critical-line statements.
-/
import ChallengeDeps
import Zeta23.ThmD.Sextuple.A1285.LineDecimal

noncomputable section

/-- A fixed-coefficient bound implies the ε-form with the same coefficient. -/
private theorem eps_form_of_fixed {q : ℝ} {N X : ℝ → ℝ}
    (hN : ∀ T, 0 ≤ N T)
    (h : ∃ T₀ : ℝ, ∀ T ≥ T₀, q * N T ≤ X T) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (q - ε) * N T ≤ X T := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := h
  refine ⟨T₀, fun T hT => ?_⟩
  have h1 : (q - ε) * N T ≤ q * N T := by
    have := mul_le_mul_of_nonneg_right (show q - ε ≤ q by linarith) (hN T)
    exact this
  exact h1.trans (hT₀ T hT)

theorem sextuple_a1285_simple_on_critical_line_decimal :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((6727949489 / 10 ^ 10 : ℝ) - ε) *
          (Ncount T (2 * T) : ℝ) ≤
        N0simple T (2 * T) :=
  eps_form_of_fixed (N := fun T => (Ncount T (2 * T) : ℝ))
    (X := fun T => (N0simple T (2 * T) : ℝ)) (fun _ => Nat.cast_nonneg _)
    Zeta23.ThmD.Sextuple.A1285.thmD₀_sextuple_6727949489

theorem sextuple_a1285_simple_on_critical_line_cumulative_decimal :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      ((6727949489 / 10 ^ 10 : ℝ) - ε) * (Ncount 0 T : ℝ) ≤
        N0simple 0 T :=
  eps_form_of_fixed (N := fun T => (Ncount 0 T : ℝ))
    (X := fun T => (N0simple 0 T : ℝ)) (fun _ => Nat.cast_nonneg _)
    Zeta23.ThmD.Sextuple.A1285.thmD₀_sextuple_cumulative_6727949489

theorem sextuple_a1285_simple_on_critical_line_6727949489 :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (6727949489 / 10 ^ 10 : ℝ) * (Ncount T (2 * T) : ℝ) ≤
        N0simple T (2 * T) :=
  Zeta23.ThmD.Sextuple.A1285.thmD₀_sextuple_6727949489

theorem sextuple_a1285_simple_on_critical_line_cumulative_6727949489 :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (6727949489 / 10 ^ 10 : ℝ) * (Ncount 0 T : ℝ) ≤
        N0simple 0 T :=
  Zeta23.ThmD.Sextuple.A1285.thmD₀_sextuple_cumulative_6727949489
