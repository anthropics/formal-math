/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.Defs.UnionCounting
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Union-count certificates from ordinary-ordinate collisions

These endgames are independent of the explicit formula.  Their only analytic input is an
eventual upper bound for the factorial collision count, or for a nonnegative pair energy.
-/

open Filter

noncomputable section

namespace Zeta23.Assembly

/-- A factorial ordinary-ordinate collision cap gives a simple-or-on-line count.
Here `κ` is the coefficient of `Σ M(γ)(M(γ)-1)`, not of `Σ M(γ)^2`. -/
theorem collision_count_certificate (Z : ZeroConfig) (κ : ℝ)
    (hC : ∀ δ > (0 : ℝ), ∀ᶠ T in atTop,
      (Z.ordinateCollision T (2 * T) : ℝ)
        ≤ (κ + δ) * (Z.N T (2 * T) : ℝ)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1 - κ / 3 - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.Nu T (2 * T) := by
  intro ε hε
  have hδ : 0 < 3 * ε := mul_pos (by norm_num) hε
  have hev : ∀ᶠ T in atTop,
      (1 - κ / 3 - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.Nu T (2 * T) := by
    filter_upwards [hC (3 * ε) hδ] with T hcap
    have hsplit : (Z.N T (2 * T) : ℝ)
        = (Z.Nu T (2 * T) : ℝ) + (Z.Nbad T (2 * T) : ℝ) := by
      exact_mod_cast Z.N_eq_Nu_add_Nbad T (2 * T)
    have hbad : 3 * (Z.Nbad T (2 * T) : ℝ)
        ≤ (Z.ordinateCollision T (2 * T) : ℝ) := by
      exact_mod_cast Z.three_Nbad_le_collision T (2 * T)
    nlinarith
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hev
  exact ⟨T₀, fun T hT => hT₀ T hT⟩

/-- An upper bound for any nonnegative ordinary-ordinate pair energy gives the same
certificate.  Here `R` is the coefficient of `Σ M(γ)^2`, so the resulting proportion is
`4/3 - R/3`. -/
theorem ordinate_energy_count_certificate (Z : ZeroConfig) (K : ℝ → ℝ → ℝ) (R : ℝ)
    (hK : ∀ T x, 0 ≤ K T x) (hK0 : ∀ T, K T 0 = 1)
    (hE : ∀ δ > (0 : ℝ), ∀ᶠ T in atTop,
      Z.ordinateEnergy T (2 * T) (K T)
        ≤ (R + δ) * (Z.N T (2 * T) : ℝ)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (4 / 3 - R / 3 - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.Nu T (2 * T) := by
  intro ε hε
  have hδ : 0 < 3 * ε := mul_pos (by norm_num) hε
  have hev : ∀ᶠ T in atTop,
      (4 / 3 - R / 3 - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.Nu T (2 * T) := by
    filter_upwards [hE (3 * ε) hδ] with T hcap
    have hsplit : (Z.N T (2 * T) : ℝ)
        = (Z.Nu T (2 * T) : ℝ) + (Z.Nbad T (2 * T) : ℝ) := by
      exact_mod_cast Z.N_eq_Nu_add_Nbad T (2 * T)
    have hbad : 3 * (Z.Nbad T (2 * T) : ℝ)
        ≤ (Z.ordinateCollision T (2 * T) : ℝ) := by
      exact_mod_cast Z.three_Nbad_le_collision T (2 * T)
    have henergy := Z.N_add_collision_le_energy T (2 * T) (K T) (hK T) (hK0 T)
    nlinarith
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hev
  exact ⟨T₀, fun T hT => hT₀ T hT⟩

end Zeta23.Assembly
