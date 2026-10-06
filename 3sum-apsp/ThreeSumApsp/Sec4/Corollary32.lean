/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Sec4.Corollary31.Limit

/-!
# Corollary 32 and the proof of Theorem 25: the time for `|W| ≤ N²/D^κ` wanted entries

Corollary 32 asks one query of Corollary 31 for each of the `|W| ≤ N²/D^κ` wanted positions, which
gives the time `O(N² log² D (D^{-γ} + D^{q-κ}))`. This bound is "a saving of D^{min{γ, κ-q}}, up to
logarithmic factors" (`corollary_32_saving`). The proof of Theorem 25 does the same with Theorem 24
and `q := κ/2`; the sum of its two times is `Theorem25.time`, which `wordRam_theorem_25` uses.
-/

public section

open Finset

namespace ThreeSumApsp

/-- Corollary 32: `N² log² D (D^{-γ} + D^{q-κ})` is "a saving of D^{min{γ, κ-q}}, up to logarithmic
factors, over the size N² of the product":
`D^{-min{γ,κ-q}} ≤ D^{-γ} + D^{q-κ} ≤ 2 D^{-min{γ,κ-q}}`. -/
theorem corollary_32_saving (D₀ : ℕ) (γ q κ : ℝ) (hD : 2 ≤ D₀) :
    (D₀ : ℝ) ^ (-(min γ (κ - q))) ≤ (D₀ : ℝ) ^ (-γ) + (D₀ : ℝ) ^ (q - κ) ∧
      (D₀ : ℝ) ^ (-γ) + (D₀ : ℝ) ^ (q - κ) ≤ 2 * (D₀ : ℝ) ^ (-(min γ (κ - q))) := by
  have hx1 : (1 : ℝ) ≤ D₀ := by exact_mod_cast (by omega : 1 ≤ D₀)
  have hx0 : (0 : ℝ) < D₀ := by linarith
  have hposγ := Real.rpow_pos_of_pos hx0 (-γ)
  have hposκ := Real.rpow_pos_of_pos hx0 (q - κ)
  have hleγ : (D₀ : ℝ) ^ (-γ) ≤ (D₀ : ℝ) ^ (-(min γ (κ - q))) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (neg_le_neg (min_le_left _ _))
  have hleκ : (D₀ : ℝ) ^ (q - κ) ≤ (D₀ : ℝ) ^ (-(min γ (κ - q))) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by have := min_le_right γ (κ - q); linarith)
  refine ⟨?_, by linarith⟩
  rcases min_choice γ (κ - q) with h | h
  · rw [h]; linarith
  · rw [h, neg_sub]; linarith

/-- Proof of Theorem 25: "As |W| ≤ N²/D^κ, this takes O(N² log² D/D^γ + |W| D^{κ/2} log D) = O(N²
log² D/D^{γ'}) time, where γ' := min{γ, κ/2}." -/
theorem Theorem25.time (γ κ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N D₀ W : ℕ, 2 ≤ D₀ → (W : ℝ) ≤ (N : ℝ) ^ 2 / (D₀ : ℝ) ^ κ →
      (N : ℝ) ^ 2 * Real.log D₀ ^ 2 / (D₀ : ℝ) ^ γ + (W : ℝ) * (D₀ : ℝ) ^ (κ / 2) * Real.log D₀
        ≤ C * ((N : ℝ) ^ 2 * Real.log D₀ ^ 2 / (D₀ : ℝ) ^ min γ (κ / 2)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 + 1 / Real.log 2, by positivity, fun N D₀ W hD hW => ?_⟩
  have hD1 : (1 : ℝ) ≤ D₀ := by exact_mod_cast (by omega : 1 ≤ D₀)
  have hD0 : (0 : ℝ) < D₀ := by linarith
  have hlog : Real.log 2 ≤ Real.log D₀ := Real.log_le_log (by norm_num) (by exact_mod_cast hD)
  have hlog0 : 0 < Real.log D₀ := hlog2.trans_le hlog
  have hG : 0 < (D₀ : ℝ) ^ min γ (κ / 2) := Real.rpow_pos_of_pos hD0 _
  have hhalf : 0 < (D₀ : ℝ) ^ (κ / 2) := Real.rpow_pos_of_pos hD0 _
  have hκ : (D₀ : ℝ) ^ κ = (D₀ : ℝ) ^ (κ / 2) * (D₀ : ℝ) ^ (κ / 2) := by
    rw [← Real.rpow_add hD0, add_halves]
  -- the preprocessing
  have hpre : (N : ℝ) ^ 2 * Real.log D₀ ^ 2 / (D₀ : ℝ) ^ γ
      ≤ (N : ℝ) ^ 2 * Real.log D₀ ^ 2 / (D₀ : ℝ) ^ min γ (κ / 2) :=
    div_le_div_of_nonneg_left (by positivity) hG
      (Real.rpow_le_rpow_of_exponent_le hD1 (min_le_left _ _))
  -- the queries; `log D ≤ log² D/ln 2` because `D ≥ 2`
  have hqueries : (W : ℝ) * (D₀ : ℝ) ^ (κ / 2) * Real.log D₀
      ≤ 1 / Real.log 2 * ((N : ℝ) ^ 2 * Real.log D₀ ^ 2 / (D₀ : ℝ) ^ min γ (κ / 2)) :=
    calc (W : ℝ) * (D₀ : ℝ) ^ (κ / 2) * Real.log D₀
        ≤ (N : ℝ) ^ 2 / (D₀ : ℝ) ^ κ * (D₀ : ℝ) ^ (κ / 2) * Real.log D₀ := by gcongr
      _ = (N : ℝ) ^ 2 * Real.log D₀ / (D₀ : ℝ) ^ (κ / 2) := by
          rw [hκ]
          field_simp
      _ ≤ (N : ℝ) ^ 2 * Real.log D₀ / (D₀ : ℝ) ^ min γ (κ / 2) :=
          div_le_div_of_nonneg_left (by positivity) hG
            (Real.rpow_le_rpow_of_exponent_le hD1 (min_le_right _ _))
      _ = (N : ℝ) ^ 2 * Real.log D₀ / (D₀ : ℝ) ^ min γ (κ / 2) * 1 := (mul_one _).symm
      _ ≤ (N : ℝ) ^ 2 * Real.log D₀ / (D₀ : ℝ) ^ min γ (κ / 2) * (Real.log D₀ / Real.log 2) := by
          gcongr
          exact (one_le_div hlog2).2 hlog
      _ = 1 / Real.log 2 * ((N : ℝ) ^ 2 * Real.log D₀ ^ 2 / (D₀ : ℝ) ^ min γ (κ / 2)) := by ring
  linarith

end ThreeSumApsp
