/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/ZeroCount/GoodHeights.lean — good heights for ξ″/ξ′ (used by the explicit-formula contour for ξ′;
cf. Zeta23/WeilEF/GoodHeights.lean for the ζ analogue).

  xiDeriv_good_heights (hF2) : ∃ C > 0, ∃ j₀, ∀ j ≥ j₀, ∃ R ∈ [j, j+1], on Im s = ±R, −1 ≤ Re s ≤ 2:
      ξ′(s) ≠ 0  and  ‖ξ″/ξ′(s)‖ ≤ C·log²(j+3).
Proof: on 1/2 ≤ Re s ≤ 2 this is the generic two-line machine
ZeroCount/Generic.good_heights_two_line at f := Y = ξ′/Γℝ (Landau partial fraction about 2 ± iR, local count,
exists_far_point) giving Y ≠ 0 and ‖Y′/Y‖ ≪ log², plus ξ″/ξ′ = Γℝ′/Γℝ + Y′/Y with Γℝ′/Γℝ ≪ log (Stirling,
ZeroCount/Y.norm_logDeriv_Gammaℝ_le_log); on −1 ≤ Re s < 1/2 reflect through s ↦ 1 − s (ξ″/ξ′(1−s) = −ξ″/ξ′(s)).
-/
import Zeta23.XiPrime.ZeroCount

open Complex Set Filter Topology MeasureTheory Metric
open scoped ComplexConjugate

noncomputable section

namespace Zeta23
namespace XiPrime
namespace ZeroCount

/-- **Good heights for ξ″/ξ′.** -/
theorem xiDeriv_good_heights (hF2 : XiDerivZerosInStrip) :
    ∃ C : ℝ, 0 < C ∧ ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j →
    ∃ R : ℝ, (j : ℝ) ≤ R ∧ R ≤ (j : ℝ) + 1 ∧
    ∀ s : ℂ, (s.im = R ∨ s.im = -R) → -1 ≤ s.re → s.re ≤ 2 →
      xiDeriv s ≠ 0 ∧ ‖logDeriv xiDeriv s‖ ≤ C * (Real.log ((j : ℝ) + 3)) ^ 2 := by
  classical
  set hs := xiDerivSeam_of_strip hF2
  set Zc := xiDerivZeros hF2 hs with hZc
  obtain ⟨Cf, t₀, hCf, ht₀2, hfa, hgrow, hlow⟩ := Yfn_generic_inputs
  have hlink' : ∀ ρ : ℂ, 0 < ρ.re → t₀ ≤ |ρ.im| → Yfn ρ = 0 → ρ ∈ Zc.carrier :=
    fun ρ hre _ h0 => (Yfn_eq_zero_iff hre).mp h0
  obtain ⟨C, hC, j₀, hgh⟩ :=
    Generic.good_heights_two_line hfa hCf hgrow hlow Zc (xiDerivZeros_link hF2 hs) hlink'
  refine ⟨C + 12, by positivity, max j₀ 2, fun j hj => ?_⟩
  have hj₀ : j₀ ≤ j := le_trans (le_max_left _ _) hj
  have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast le_trans (le_max_right _ _) hj
  obtain ⟨R, hR1, hR2, hright⟩ := hgh j hj₀
  refine ⟨R, hR1, hR2, ?_⟩
  set Lg : ℝ := Real.log ((j : ℝ) + 3) with hLg
  have hLg1 : 1 ≤ Lg := by
    rw [hLg, ← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith
  have hlogR : Real.log (R + 3) ≤ 2 * Lg := by
    have hlog2 : Real.log 2 ≤ Lg := by rw [hLg]; exact Real.log_le_log (by norm_num) (by linarith)
    calc Real.log (R + 3) ≤ Real.log (2 * ((j:ℝ) + 3)) := Real.log_le_log (by linarith) (by linarith)
      _ = Real.log 2 + Lg := by rw [Real.log_mul (by norm_num) (by linarith)]
      _ ≤ 2 * Lg := by linarith
  -- the right half 1/2 ≤ Re s ≤ 2: Y-part from the generic machine, Γℝ-part by Stirling
  have right_half : ∀ s : ℂ, (s.im = R ∨ s.im = -R) → 1 / 2 ≤ s.re → s.re ≤ 2 →
      xiDeriv s ≠ 0 ∧ ‖logDeriv xiDeriv s‖ ≤ (C + 12) * Lg ^ 2 := by
    intro s hsR hσ1 hσ2
    have hsre : 0 < s.re := by linarith
    obtain ⟨hY, hYb⟩ := hright s hsR hσ1 hσ2
    have hξ : xiDeriv s ≠ 0 := fun h => hY ((Yfn_eq_zero_iff hsre).mpr h)
    have habs : |s.im| = R := by
      rcases hsR with h | h
      · rw [h, abs_of_nonneg (by linarith)]
      · rw [h, abs_neg, abs_of_nonneg (by linarith)]
    have hΓ : ‖logDeriv Gammaℝ s‖ ≤ 2 * Lg + 5 := by
      have h2 : 2 ≤ |s.im| := by rw [habs]; linarith
      have := norm_logDeriv_Gammaℝ_le_log hsre (by linarith) h2
      rw [habs] at this; linarith
    refine ⟨hξ, ?_⟩
    rw [logDeriv_xiDeriv_eq hsre hξ]
    refine (norm_add_le _ _).trans ?_
    have : Lg ≤ Lg ^ 2 := by nlinarith
    nlinarith [hYb, hΓ]
  -- now all of −1 ≤ Re s ≤ 2, by reflection through s ↦ 1 − s on the left part
  intro s hsR hσ1 hσ2
  rcases le_or_gt (1 / 2 : ℝ) s.re with h | h
  · exact right_half s hsR h hσ2
  · have h1 : (1 - s).im = R ∨ (1 - s).im = -R := by
      rcases hsR with h' | h' <;> simp [h']
    obtain ⟨hne, hb⟩ := right_half (1 - s) h1 (by simp; linarith) (by simp; linarith)
    refine ⟨fun h0 => hne (by rw [xiDeriv_one_sub, h0, neg_zero]), ?_⟩
    have : logDeriv xiDeriv s = -logDeriv xiDeriv (1 - s) := by
      rw [logDeriv_xiDeriv_one_sub]; ring
    rw [this, norm_neg]
    exact hb

end ZeroCount
end XiPrime
end Zeta23
