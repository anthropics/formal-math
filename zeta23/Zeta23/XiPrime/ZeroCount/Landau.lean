/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/ZeroCount/Landau.lean — Landau's partial fraction for Y′/Y on discs centred at 2+it, and the
LOCAL COUNT of zeros of ξ′.

These are the f := Y = ξ′/Γℝ instances of the generic two-line machine Zeta23/XiPrime/ZeroCount/Generic.lean
(which packages Zeta23.WeilEF.logDeriv_partial_fraction_disk, the halving ρ ↦ 1−ρ̄ and the window geometry);
the Y-specific inputs are ZeroCount/Y.lean's Yfn_analyticOnNhd_disc, Yfn_growth (‖Y‖ ≤ C|Im|⁴ on
1/8 ≤ Re ≤ 4) and two_line_lower (‖Y(2+it)‖ ≥ 1).
Outputs:
  * Yfn_logDeriv_partial_fraction — for |t| ≥ t₁: the zeros of Y within 22/25·91/50 of 2+it form a finite
    set Z with Σ_Z ord ≤ C log(|t|+3), and Y′/Y(s) = Σ_Z ord/(s−ρ) + O(log(|t|+3)) on the 3/2-ball;
  * half_count_large, xiDeriv_local_count (hF2) (hs) — N_{ξ′}(t, t+1] ≤ A₀ log(|t|+3) for all real t.
-/
import Zeta23.XiPrime.ZeroCount.Y
import Zeta23.XiPrime.ZeroCount.Generic

open Complex Set Filter Topology Metric
open scoped ComplexConjugate

noncomputable section

namespace Zeta23
namespace XiPrime
namespace ZeroCount

/-- the generic two-line data (hfa, hgrow, hlow') for f := Y, packaged. -/
theorem Yfn_generic_inputs : ∃ (Cf t₀ : ℝ), 0 < Cf ∧ 2 ≤ t₀ ∧
    (∀ t : ℝ, t₀ ≤ |t| → AnalyticOnNhd ℂ Yfn (closedBall (2 + t * I) (91 / 50))) ∧
    (∀ s : ℂ, 1 / 8 ≤ s.re → s.re ≤ 4 → 2 ≤ |s.im| → ‖Yfn s‖ ≤ Cf * |s.im| ^ 4) ∧
    (∀ t : ℝ, t₀ ≤ |t| → 1 ≤ ‖Yfn (2 + t * I)‖) := by
  obtain ⟨Cf, hCf, hgrow⟩ := Yfn_growth
  obtain ⟨t₁, ht₁, hlow⟩ := two_line_lower
  exact ⟨Cf, t₁, hCf, ht₁, fun t _ => Yfn_analyticOnNhd_disc t (by norm_num), hgrow,
    fun t ht => (hlow t ht).2⟩

/-- **Landau partial fraction for Y′/Y around 2+it** (|t| ≥ t₁). -/
theorem Yfn_logDeriv_partial_fraction : ∃ C t₁ : ℝ, 0 < C ∧ 4 ≤ t₁ ∧ ∀ t : ℝ, t₁ ≤ |t| →
    Yfn (2 + t * I) ≠ 0 ∧
    ∃ Z : Finset ℂ,
      (↑Z = {ρ ∈ closedBall (2 + t * I) (22 / 25 * (91 / 50)) | Yfn ρ = 0}) ∧
      ((∑ ρ ∈ Z, (analyticOrderNatAt Yfn ρ : ℝ)) ≤ C * Real.log (|t| + 3)) ∧
      ∀ s ∈ closedBall (2 + t * I) (3 / 2), Yfn s ≠ 0 →
        ‖logDeriv Yfn s - ∑ ρ ∈ Z, (analyticOrderNatAt Yfn ρ : ℂ) / (s - ρ)‖
          ≤ C * Real.log (|t| + 3) := by
  obtain ⟨Cf, t₀, hCf, -, hfa, hgrow, hlow⟩ := Yfn_generic_inputs
  obtain ⟨C, t₁, hC, ht₁4, -, h⟩ := Generic.logDeriv_partial_fraction_two_line hfa hCf hgrow hlow
  exact ⟨C, t₁, hC, ht₁4, h⟩

/-! ### the local count -/

section LocalCount

variable (hF2 : XiDerivZerosInStrip) (hs : XiDerivSeam)

/-- the link between the configuration xiDerivZeros and f := Y: every configuration point with β ≥ 1/2 is a
zero of Y of the same order. -/
theorem xiDerivZeros_link : ∀ ρ ∈ (xiDerivZeros hF2 hs).carrier, 1 / 2 ≤ ρ.re →
    Yfn ρ = 0 ∧ analyticOrderNatAt Yfn ρ = (xiDerivZeros hF2 hs).mult ρ := by
  intro ρ hρ _
  have hρ0 : xiDeriv ρ = 0 := hρ
  have h0 : 0 < ρ.re := (hF2 ρ hρ0).1
  exact ⟨(Yfn_eq_zero_iff h0).mpr hρ0, by rw [xiDerivZeros_mult, analyticOrderNatAt_Yfn h0]⟩

/-- the β ≥ 1/2 half of the window (t, t+1] counted with multiplicity is ≪ log(|t|+3), for |t + 1/2| ≥ t₁. -/
theorem half_count_large : ∃ A₁ t₁ : ℝ, 0 < A₁ ∧ ∀ t : ℝ, t₁ ≤ |t + 1 / 2| →
    (∑ᶠ ρ ∈ (xiDerivZeros hF2 hs).window t (t + 1) ∩ {ρ | 1 / 2 ≤ ρ.re},
      ((xiDerivZeros hF2 hs).mult ρ : ℝ)) ≤ A₁ * Real.log (|t| + 3) := by
  obtain ⟨Cf, t₀, hCf, -, hfa, hgrow, hlow⟩ := Yfn_generic_inputs
  exact Generic.half_count_large_two_line hfa hCf hgrow hlow (xiDerivZeros hF2 hs)
    (xiDerivZeros_link hF2 hs)

/-- **Local count for ξ′** ([XF′ (F3)], the ξ′-analogue of [Tit86, Thm 9.2]): N_{ξ′}(t,t+1] ≤ A₀ log(|t|+3)
for all real t. -/
theorem xiDeriv_local_count : ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ t : ℝ,
    ((xiDerivZeros hF2 hs).N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3) := by
  obtain ⟨Cf, t₀, hCf, -, hfa, hgrow, hlow⟩ := Yfn_generic_inputs
  exact Generic.local_count_two_line hfa hCf hgrow hlow (xiDerivZeros hF2 hs) (xiDerivZeros_link hF2 hs)

end LocalCount

end ZeroCount
end XiPrime
end Zeta23
