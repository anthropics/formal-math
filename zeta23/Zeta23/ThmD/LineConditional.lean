/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.ThmD.Mult
import Zeta23.Assembly.UnionCollision

/-!
# Conditional critical-line bounds from ordinary-ordinate collisions

These statements isolate arithmetic estimates that would improve the unconditional
`67.25%` endpoint.  The hypotheses are explicit and are not part of `PaperInputs`.
A collision coefficient strictly below `0.30`, or a nonnegative energy coefficient
strictly below `1.30`, gives an eventual fixed `70%` simple-on-line bound.
-/

open Filter

noncomputable section

namespace Zeta23.ThmD

/-- A factorial ordinary-ordinate collision coefficient `κ` gives simple-on-line
proportion `1 - κ` in dyadic windows. -/
theorem thmD₀_simple_mult_of_collision (κ : ℝ)
    (hcollision : ∀ δ > (0 : ℝ), ∀ᶠ T in atTop,
      (zetaZeroConfig.ordinateCollision T (2 * T) : ℝ) ≤
        (κ + δ) * (Ncount T (2 * T) : ℝ)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1 - κ - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  have hC : ∀ δ > (0 : ℝ), ∀ᶠ T in atTop,
      (zetaZeroConfig.ordinateCollision T (2 * T) : ℝ) ≤
        (κ + δ) * (zetaZeroConfig.N T (2 * T) : ℝ) := by
    simpa only [zetaZeroConfig_N] using hcollision
  simpa only [zetaZeroConfig_N, zetaZeroConfig_N0s] using
    Assembly.simple_line_collision_count_certificate zetaZeroConfig κ hC

/-- Cumulative version of `thmD₀_simple_mult_of_collision`, from the same
dyadic collision hypothesis. -/
theorem thmD₀_simple_mult_cumulative_of_collision (κ : ℝ)
    (hcollision : ∀ δ > (0 : ℝ), ∀ᶠ T in atTop,
      (zetaZeroConfig.ordinateCollision T (2 * T) : ℝ) ≤
        (κ + δ) * (Ncount T (2 * T) : ℝ)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1 - κ - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  cumulative_of_dyadic zetaSeam paperInputs_zeta.RvM
    (fun _ _ _ => N0simple_add' zetaSeam)
    (thmD₀_simple_mult_of_collision κ hcollision)

/-- A nonnegative ordinary-ordinate energy coefficient `R` gives simple-on-line
proportion `2 - R` in dyadic windows. -/
theorem thmD₀_simple_mult_of_ordinateEnergy (K : ℝ → ℝ → ℝ) (R : ℝ)
    (hK : ∀ T x, 0 ≤ K T x) (hK0 : ∀ T, K T 0 = 1)
    (henergy : ∀ δ > (0 : ℝ), ∀ᶠ T in atTop,
      zetaZeroConfig.ordinateEnergy T (2 * T) (K T) ≤
        (R + δ) * (Ncount T (2 * T) : ℝ)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 - R - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  have hE : ∀ δ > (0 : ℝ), ∀ᶠ T in atTop,
      zetaZeroConfig.ordinateEnergy T (2 * T) (K T) ≤
        (R + δ) * (zetaZeroConfig.N T (2 * T) : ℝ) := by
    simpa only [zetaZeroConfig_N] using henergy
  simpa only [zetaZeroConfig_N, zetaZeroConfig_N0s] using
    Assembly.simple_line_ordinate_energy_count_certificate zetaZeroConfig K R hK hK0 hE

/-- Cumulative version of `thmD₀_simple_mult_of_ordinateEnergy`. -/
theorem thmD₀_simple_mult_cumulative_of_ordinateEnergy
    (K : ℝ → ℝ → ℝ) (R : ℝ)
    (hK : ∀ T x, 0 ≤ K T x) (hK0 : ∀ T, K T 0 = 1)
    (henergy : ∀ δ > (0 : ℝ), ∀ᶠ T in atTop,
      zetaZeroConfig.ordinateEnergy T (2 * T) (K T) ≤
        (R + δ) * (Ncount T (2 * T) : ℝ)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 - R - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  cumulative_of_dyadic zetaSeam paperInputs_zeta.RvM
    (fun _ _ _ => N0simple_add' zetaSeam)
    (thmD₀_simple_mult_of_ordinateEnergy K R hK hK0 henergy)

private theorem fixed_lower_of_eps_form {c q : ℝ} {N lower : ℝ → ℝ}
    (hq : q < c)
    (h : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (c - ε) * N T ≤ lower T) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, q * N T ≤ lower T := by
  obtain ⟨T₀, hT₀⟩ := h (c - q) (sub_pos.mpr hq)
  refine ⟨T₀, fun T hT => ?_⟩
  convert hT₀ T hT using 1
  ring

/-- Any fixed collision saving below `0.30` proves an eventual fixed `70%`
simple-on-line proportion in dyadic windows. -/
theorem thmD₀_simple_mult_70_of_collision (κ : ℝ) (hκ : κ < 3 / 10)
    (hcollision : ∀ δ > (0 : ℝ), ∀ᶠ T in atTop,
      (zetaZeroConfig.ordinateCollision T (2 * T) : ℝ) ≤
        (κ + δ) * (Ncount T (2 * T) : ℝ)) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (7 / 10 : ℝ) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  apply fixed_lower_of_eps_form (c := 1 - κ)
  · linarith
  · exact thmD₀_simple_mult_of_collision κ hcollision

/-- Cumulative fixed `70%` conclusion from a collision coefficient below `0.30`. -/
theorem thmD₀_simple_mult_cumulative_70_of_collision (κ : ℝ) (hκ : κ < 3 / 10)
    (hcollision : ∀ δ > (0 : ℝ), ∀ᶠ T in atTop,
      (zetaZeroConfig.ordinateCollision T (2 * T) : ℝ) ≤
        (κ + δ) * (Ncount T (2 * T) : ℝ)) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (7 / 10 : ℝ) * (Ncount 0 T : ℝ) ≤ N0simple 0 T := by
  apply fixed_lower_of_eps_form (c := 1 - κ)
  · linarith
  · exact thmD₀_simple_mult_cumulative_of_collision κ hcollision

/-- Any fixed energy saving below `1.30` proves an eventual fixed `70%`
simple-on-line proportion in dyadic windows. -/
theorem thmD₀_simple_mult_70_of_ordinateEnergy (K : ℝ → ℝ → ℝ) (R : ℝ)
    (hR : R < 13 / 10)
    (hK : ∀ T x, 0 ≤ K T x) (hK0 : ∀ T, K T 0 = 1)
    (henergy : ∀ δ > (0 : ℝ), ∀ᶠ T in atTop,
      zetaZeroConfig.ordinateEnergy T (2 * T) (K T) ≤
        (R + δ) * (Ncount T (2 * T) : ℝ)) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (7 / 10 : ℝ) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  apply fixed_lower_of_eps_form (c := 2 - R)
  · linarith
  · exact thmD₀_simple_mult_of_ordinateEnergy K R hK hK0 henergy

/-- Cumulative fixed `70%` conclusion from an energy coefficient below `1.30`. -/
theorem thmD₀_simple_mult_cumulative_70_of_ordinateEnergy
    (K : ℝ → ℝ → ℝ) (R : ℝ) (hR : R < 13 / 10)
    (hK : ∀ T x, 0 ≤ K T x) (hK0 : ∀ T, K T 0 = 1)
    (henergy : ∀ δ > (0 : ℝ), ∀ᶠ T in atTop,
      zetaZeroConfig.ordinateEnergy T (2 * T) (K T) ≤
        (R + δ) * (Ncount T (2 * T) : ℝ)) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (7 / 10 : ℝ) * (Ncount 0 T : ℝ) ≤ N0simple 0 T := by
  apply fixed_lower_of_eps_form (c := 2 - R)
  · linarith
  · exact thmD₀_simple_mult_cumulative_of_ordinateEnergy K R hK hK0 henergy

end Zeta23.ThmD
