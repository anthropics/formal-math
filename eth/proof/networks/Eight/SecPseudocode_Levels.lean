/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Eight.Level.Defs
public import SingleBitPieces.SecPseudocode_Levels
import Mathlib.Tactic

/-! # The section «The algorithm in pseudocode» with ρ = 11/12: the upper estimate of the numbers e_ℓ and their limit

The counterpart of proof/networks/SingleBitPieces/SecPseudocode_Levels.lean for ρ = 11/12. The file
is named after that counterpart; in the paper this is Section 8. `Eight.Level.levelE`
(proof/networks/Eight/Level/Defs.lean) is e_ℓ of the display of Section 8, e₀ = 1/2, e_{ℓ+1} = (ρ +
2/K_ℓ)·e_ℓ + 2/K_ℓ, with ρ = 11/12 (`Eight.rho`); K_ℓ is `Paper.levelK`.
This file proves e_ℓ ≥ 0 (`levelE_nonneg`), the upper estimate e_ℓ ≤ 0.56·ρ^ℓ of Section 8
(`levelE_le`), e_ℓ → 0 (`levelE_tendsto`), and the form in which the limit is used (`exists_level`).
That (K_ℓ, e_ℓ) is achievable is not proved here.
The upper estimate is proved in the sharper form e_ℓ ≤ 0.56·ρ^ℓ − 3.8/K_ℓ, which goes through the
induction because ρ ≥ 7/8 and K_{ℓ+1} ≥ 19·K_ℓ.
From proof/networks/SingleBitPieces/SecPseudocode_Levels.lean only facts on K_ℓ are used, among them
`SingleBitPieces.SecPseudocode_Levels.levelK_pos` and `levelK_succ_ge`; they do not mention ρ. -/

public section

namespace Eight.Level

open Paper SingleBitPieces.SecPseudocode_Levels

/-- ρ = 11/12 is positive. -/
theorem rho_pos : 0 < rho := by norm_num [rho]

/-- ρ = 11/12 < 1. -/
theorem rho_lt_one : rho < 1 := by norm_num [rho]

/-- ρ = 11/12 ≥ 7/8. -/
theorem rho_ge : 7 / 8 ≤ rho := by norm_num [rho]

/-- e_ℓ is not negative. -/
theorem levelE_nonneg (ℓ : ℕ) : 0 ≤ levelE ℓ := by
  induction ℓ with
  | zero => norm_num [levelE]
  | succ ℓ ih =>
    have hK := levelK_pos ℓ
    have hρ := rho_pos
    simp only [levelE]
    positivity

/-- The sharper form of the upper estimate: e_ℓ ≤ 0.56·ρ^ℓ − 3.8/K_ℓ. Not a sentence of the paper. -/
theorem levelE_le_sub (ℓ : ℕ) : levelE ℓ ≤ 0.56 * rho ^ ℓ - 3.8 / levelK ℓ := by
  induction ℓ with
  | zero => norm_num [levelE, levelK]
  | succ ℓ ih =>
    have hK := levelK_pos ℓ
    have hK' := levelK_pos (ℓ + 1)
    have hρ0 := rho_pos
    have hρ7 := rho_ge
    have hρ1 : rho ^ ℓ ≤ 1 := pow_le_one₀ hρ0.le rho_lt_one.le
    have hρp : 0 < rho ^ ℓ := pow_pos hρ0 ℓ
    obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 1 / levelK ℓ := ⟨_, rfl⟩
    have ha0 : 0 < a := by rw [ha]; positivity
    have hb : 3.8 / (levelK (ℓ + 1) : ℝ) ≤ 0.2 * a := by
      rw [ha, div_le_iff₀ hK']
      have h := levelK_succ_ge ℓ
      have e : 0.2 * (1 / (levelK ℓ : ℝ)) * (levelK (ℓ + 1) : ℝ) = 0.2 * ((levelK (ℓ + 1) : ℝ) / levelK ℓ) := by ring
      rw [e]
      have h2 : 19 ≤ (levelK (ℓ + 1) : ℝ) / levelK ℓ := (le_div_iff₀ hK).2 h
      linarith
    have e1 : (2 : ℝ) / levelK ℓ = 2 * a := by rw [ha]; ring
    have e2 : (3.8 : ℝ) / levelK ℓ = 3.8 * a := by rw [ha]; ring
    rw [e2] at ih
    simp only [levelE]
    rw [e1, pow_succ]
    have h1 : (rho + 2 * a) * levelE ℓ ≤ (rho + 2 * a) * (0.56 * rho ^ ℓ - 3.8 * a) := mul_le_mul_of_nonneg_left ih (by positivity)
    have h2 : 0 ≤ a * a := by positivity
    have h3 : a * rho ^ ℓ ≤ a := by nlinarith
    have h4 : 7 / 8 * a ≤ rho * a := by nlinarith
    nlinarith

/-- Section 8: «precisely, unrolling … gives ½ρ^ℓ ≤ e_ℓ ≤ 0.56 ρ^ℓ», the second inequality, with ρ =
11/12. Same as in the paper. -/
theorem levelE_le (ℓ : ℕ) : levelE ℓ ≤ 0.56 * rho ^ ℓ := by
  have h1 := levelE_le_sub ℓ
  have h2 : 0 ≤ 3.8 / (levelK ℓ : ℝ) := by have := levelK_pos ℓ; positivity
  linarith

/-- Section 8: «e_ℓ → 0». Same as in the paper. -/
theorem levelE_tendsto : Filter.Tendsto levelE Filter.atTop (nhds 0) := by
  have h1 : Filter.Tendsto (fun ℓ : ℕ => 0.56 * rho ^ ℓ) Filter.atTop (nhds 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one rho_pos.le rho_lt_one).const_mul (0.56 : ℝ)
    rwa [mul_zero] at h
  exact squeeze_zero levelE_nonneg levelE_le h1

/-- The form in which «e_ℓ → 0» is used for Theorem 2: for every η > 0 and every K₀ there is a level
ℓ with K_ℓ ≥ K₀ and e_ℓ ≤ η. Not a sentence of the paper; it follows from the limit and from ℓ <
K_ℓ. -/
theorem exists_level {η : ℝ} (hη : 0 < η) (K₀ : ℕ) : ∃ ℓ, K₀ ≤ levelK ℓ ∧ levelE ℓ ≤ η := by
  obtain ⟨ℓ₁, h1⟩ := Filter.eventually_atTop.1 (levelE_tendsto.eventually_le_const hη)
  exact ⟨max ℓ₁ K₀, (le_max_right _ _).trans (lt_levelK _).le, h1 _ (le_max_left _ _)⟩

end Eight.Level
