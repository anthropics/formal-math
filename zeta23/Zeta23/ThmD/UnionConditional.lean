/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.ThmD.Union
import Zeta23.Assembly.UnionCollision

/-!
# Conditional simple-or-on-line endpoint from ordinary-ordinate collisions

These statements isolate the additional arithmetic estimate that would raise the
unconditional endpoint.  The hypotheses are explicit and are not part of
`PaperInputs`.
-/

open Filter

noncomputable section

namespace Zeta23.ThmD

/-- Conditional dyadic endpoint from the missing factorial ordinary-ordinate
collision estimate.  The hypothesis says
`Σ_γ M_T(γ)(M_T(γ)-1) ≤ (((cStar 1)⁻¹-1)+o(1)) N(T,2T)`. -/
theorem thmD₀_union_of_collision
    (hcollision : ∀ δ > (0 : ℝ), ∀ᶠ T in atTop,
      (zetaZeroConfig.ordinateCollision T (2 * T) : ℝ) ≤
        (((cStar 1)⁻¹ - 1) + δ) * (Ncount T (2 * T) : ℝ)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1 - ((cStar 1)⁻¹ - 1) / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤
        ((N0 T (2 * T) + Nsimple T (2 * T) - N0simple T (2 * T) : ℕ) : ℝ) := by
  have hC : ∀ δ > (0 : ℝ), ∀ᶠ T in atTop,
      (zetaZeroConfig.ordinateCollision T (2 * T) : ℝ) ≤
        (((cStar 1)⁻¹ - 1) + δ) *
          (zetaZeroConfig.N T (2 * T) : ℝ) := by
    simpa only [zetaZeroConfig_N] using hcollision
  simpa only [zetaZeroConfig_N, zetaZeroConfig_Nu_eq] using
    Assembly.collision_count_certificate zetaZeroConfig
      ((cStar 1)⁻¹ - 1) hC

/-- Cumulative version of `thmD₀_union_of_collision`, with the same explicit
dyadic collision hypothesis. -/
theorem thmD₀_union_cumulative_of_collision
    (hcollision : ∀ δ > (0 : ℝ), ∀ᶠ T in atTop,
      (zetaZeroConfig.ordinateCollision T (2 * T) : ℝ) ≤
        (((cStar 1)⁻¹ - 1) + δ) * (Ncount T (2 * T) : ℝ)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1 - ((cStar 1)⁻¹ - 1) / 3 - ε) * (Ncount 0 T : ℝ) ≤
        ((N0 0 T + Nsimple 0 T - N0simple 0 T : ℕ) : ℝ) := by
  apply cumulative_of_dyadic zetaSeam paperInputs_zeta.RvM
      (f := fun a b => N0 a b + Nsimple a b - N0simple a b)
      (fun a b d hab hbd => ?_) (thmD₀_union_of_collision hcollision)
  simpa only [zetaZeroConfig_Nu_eq] using
    Assembly.Nu_add zetaZeroConfig hab hbd

/-- Conditional dyadic endpoint from a nonnegative ordinary-ordinate pair energy
with Montgomery--Taylor second-moment coefficient. -/
theorem thmD₀_union_of_ordinateEnergy (K : ℝ → ℝ → ℝ)
    (hK : ∀ T x, 0 ≤ K T x) (hK0 : ∀ T, K T 0 = 1)
    (henergy : ∀ δ > (0 : ℝ), ∀ᶠ T in atTop,
      zetaZeroConfig.ordinateEnergy T (2 * T) (K T) ≤
        ((cStar 1)⁻¹ + δ) * (Ncount T (2 * T) : ℝ)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1 - ((cStar 1)⁻¹ - 1) / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤
        ((N0 T (2 * T) + Nsimple T (2 * T) - N0simple T (2 * T) : ℕ) : ℝ) := by
  have hE : ∀ δ > (0 : ℝ), ∀ᶠ T in atTop,
      zetaZeroConfig.ordinateEnergy T (2 * T) (K T) ≤
        ((cStar 1)⁻¹ + δ) * (zetaZeroConfig.N T (2 * T) : ℝ) := by
    simpa only [zetaZeroConfig_N] using henergy
  have h := Assembly.ordinate_energy_count_certificate zetaZeroConfig K
    (cStar 1)⁻¹ hK hK0 hE
  have hconst : 4 / 3 - (cStar 1)⁻¹ / 3 =
      1 - ((cStar 1)⁻¹ - 1) / 3 := by
    ring
  rw [hconst] at h
  simpa only [zetaZeroConfig_N, zetaZeroConfig_Nu_eq] using h

/-- Cumulative version of `thmD₀_union_of_ordinateEnergy`. -/
theorem thmD₀_union_cumulative_of_ordinateEnergy (K : ℝ → ℝ → ℝ)
    (hK : ∀ T x, 0 ≤ K T x) (hK0 : ∀ T, K T 0 = 1)
    (henergy : ∀ δ > (0 : ℝ), ∀ᶠ T in atTop,
      zetaZeroConfig.ordinateEnergy T (2 * T) (K T) ≤
        ((cStar 1)⁻¹ + δ) * (Ncount T (2 * T) : ℝ)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1 - ((cStar 1)⁻¹ - 1) / 3 - ε) * (Ncount 0 T : ℝ) ≤
        ((N0 0 T + Nsimple 0 T - N0simple 0 T : ℕ) : ℝ) := by
  apply cumulative_of_dyadic zetaSeam paperInputs_zeta.RvM
      (f := fun a b => N0 a b + Nsimple a b - N0simple a b)
      (fun a b d hab hbd => ?_)
      (thmD₀_union_of_ordinateEnergy K hK hK0 henergy)
  simpa only [zetaZeroConfig_Nu_eq] using
    Assembly.Nu_add zetaZeroConfig hab hbd

end Zeta23.ThmD
