/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.RunningTimes.Sec5.Corollary40.MvHintedTimes
public import ThreeSumApsp.RunningTimes.Sec5.Corollary40.UMvHintedTimes
public import ThreeSumApsp.RunningTimes.Sec5.Corollary40.VHintedTimes

/-!
# Corollary 40 on the word RAM

The route, as in the paper.  Each of the three hinted problems is solved in phases by programs that
use a data structure for a thin matrix product: the phase after the hint preprocesses, the last
phase asks queries.  For `τ < 1/18` it is the data structure of Corollary 26
(`wordRam_corollary_40_times`), for `τ < ε*` ("General τ") that of Corollary 31 with suitable
parameters (`wordRam_corollary_40_general_times`); for uMv-hinted uMv the conditions are
`τ₁ < τ₂/18` and `τ₁ < ε* τ₂`.  "In each case the phases beat the conjectured
bounds whatever the value of ω": every exponent is below the conjectured one, and larger exponents
are easier to achieve (`AchievesVHinted.mono` and its two companions).  So the three conjectures
fail for `τ < ε*`, by `not_conjecture52_of_achieves` and its two companions, and with them for
`τ < 1/18 < ε*` (`Corollary40.fail_mono`, `wordRam_corollary_40_fail`).
-/

public section

open ThreeSumApsp.WordRam

namespace ThreeSumApsp

namespace WordRam

/-! ## Larger exponents are easier to achieve -/

/-- A bound `O(n^a)` is also a bound `O(n^{a'})` for `a ≤ a'`, with a constant that is not negative.
-/
private theorem Within.mono {t : ℕ} {C : ℝ} {n : ℕ} {a a' : ℝ} (h : Within t C n a) (hn : 1 ≤ n)
    (ha : a ≤ a') : Within t (max C 0) n a' := by
  unfold Within at *
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ a ≤ (n : ℝ) ^ a' := Real.rpow_le_rpow_of_exponent_le hn1 ha
  have hnonneg : (0 : ℝ) ≤ (n : ℝ) ^ a := Real.rpow_nonneg (by linarith) _
  calc (t : ℝ) ≤ C * ((n : ℝ) ^ a + 1) := h
    _ ≤ max C 0 * ((n : ℝ) ^ a + 1) := by gcongr; exact le_max_left _ _
    _ ≤ max C 0 * ((n : ℝ) ^ a' + 1) := by
      have := le_max_right C 0
      gcongr

/-- v-hinted Mv: larger exponents for Phases 2 and 3 are easier to achieve. -/
theorem AchievesVHinted.mono {τ : ℝ} ⦃a₂ a₃ a₂' a₃' : ℝ⦄ (h : AchievesVHinted τ a₂ a₃)
    (h₂ : a₂ ≤ a₂') (h₃ : a₃ ≤ a₃') : AchievesVHinted τ a₂' a₃' := by
  obtain ⟨P₁, P₂, P₃, b, C, a₁, h⟩ := h
  refine ⟨P₁, P₂, P₃, b, max C 0, a₁, fun n hn M V i bits hb => ?_⟩
  obtain ⟨t₁, t₂, t₃, w₁, w₂, w₃, hr⟩ := h n hn M V i bits hb
  exact ⟨t₁, t₂, t₃, w₁.mono hn le_rfl, w₂.mono hn h₂, w₃.mono hn h₃, hr⟩

/-- Mv-hinted Mv: larger exponents for Phases 2 and 3 are easier to achieve. -/
theorem AchievesMvHinted.mono {τ : ℝ} ⦃a₂ a₃ a₂' a₃' : ℝ⦄ (h : AchievesMvHinted τ a₂ a₃)
    (h₂ : a₂ ≤ a₂') (h₃ : a₃ ≤ a₃') : AchievesMvHinted τ a₂' a₃' := by
  obtain ⟨P₁, P₂, P₃, b, C, a₁, h⟩ := h
  refine ⟨P₁, P₂, P₃, b, max C 0, a₁, fun n hn N V I j bits hb => ?_⟩
  obtain ⟨t₁, t₂, t₃, w₁, w₂, w₃, hr⟩ := h n hn N V I j bits hb
  exact ⟨t₁, t₂, t₃, w₁.mono hn le_rfl, w₂.mono hn h₂, w₃.mono hn h₃, hr⟩

/-- uMv-hinted uMv: larger exponents for Phases 2, 3 and 4 are easier to achieve. -/
theorem AchievesUMvHinted.mono {τ₁ τ₂ : ℝ} ⦃a₂ a₃ a₄ a₂' a₃' a₄' : ℝ⦄
    (h : AchievesUMvHinted τ₁ τ₂ a₂ a₃ a₄) (h₂ : a₂ ≤ a₂') (h₃ : a₃ ≤ a₃') (h₄ : a₄ ≤ a₄') :
    AchievesUMvHinted τ₁ τ₂ a₂' a₃' a₄' := by
  obtain ⟨P₁, P₂, P₃, P₄, b, C, a₁, h⟩ := h
  refine ⟨P₁, P₂, P₃, P₄, b, max C 0, a₁, fun n hn U N V I J i j bits hb => ?_⟩
  obtain ⟨t₁, t₂, t₃, t₄, w₁, w₂, w₃, w₄, hr⟩ := h n hn U N V I J i j bits hb
  exact ⟨t₁, t₂, t₃, t₄, w₁.mono hn le_rfl, w₂.mono hn h₂, w₃.mono hn h₃, w₄.mono hn h₄, hr⟩

end WordRam

/-! ## The running times -/

/-- **Corollary 40**, on the word RAM: the running times for `τ < 1/18`. -/
theorem wordRam_corollary_40_times : Items.Corollary_40_times :=
  ⟨fun _ hpos hlt =>
      ⟨Light.Sec5.achievesVHinted_of_lt_eighteenth hpos hlt,
          Light.Sec5.achievesMvHinted_of_lt_eighteenth hpos hlt⟩,
    fun _ _ hpos hlt hτ₂ => Light.Sec5.achievesUMvHinted_of_lt_eighteenth hpos hlt hτ₂⟩

/-- **The proof of Corollary 40**, paragraph "General τ", on the word RAM: the running times for
`τ < ε*`. -/
theorem wordRam_corollary_40_general_times : Items.Corollary_40_general_times := by
  refine ⟨fun τ hpos hlt => ?_,
    fun _ _ hpos hlt hτ₂ => Light.Sec5.achievesUMvHinted_of_lt_epsStar hpos hlt hτ₂⟩
  -- one choice of the parameters, and so one saving γ, serves both problems
  obtain ⟨c, θ, ε, γ, p, hτ⟩ := exists_genParams hlt
  have hstar := sec4_epsStar_numeric.2
  exact ⟨γ, p.γ_pos, Light.Sec5.achievesVHinted_of_genParams p hpos hτ,
    Light.Sec5.achievesMvHinted_of_genParams p hpos hτ (by linarith)⟩

/-! ## The conjectures fail -/

/-- Conjectures that fail up to `τ₀` fail up to every smaller bound. -/
theorem Corollary40.fail_mono {τ₀ τ₀' : ℝ} (h0 : 0 ≤ τ₀') (hle : τ₀' ≤ τ₀)
    (h : Items.Corollary_40_fail τ₀) : Items.Corollary_40_fail τ₀' :=
  ⟨fun τ ω hpos hlt hω => h.1 τ ω hpos (hlt.trans_le hle) hω,
    fun τ₁ τ₂ ω₂ ω₃ hpos hlt hτ₂ hω₂ hω₃ => h.2 τ₁ τ₂ ω₂ ω₃ hpos
      (hlt.trans_le (mul_le_mul_of_nonneg_right hle (pos_of_mul_pos_right (hpos.trans hlt) h0).le))
      hτ₂ hω₂ hω₃⟩

/-- For `τ < ε*` every exponent is below the conjectured one. -/
private theorem Corollary40.fail_general : Items.Corollary_40_fail epsStar := by
  obtain ⟨hstar0, hstar1⟩ := sec4_epsStar_numeric
  refine ⟨fun τ ω hpos hlt hω => ?_, fun τ₁ τ₂ ω₂ ω₃ hpos hlt hτ₂ hω₂ hω₃ => ?_⟩
  · obtain ⟨γ, hγ, hv, hm⟩ := wordRam_corollary_40_general_times.1 τ hpos hlt
    have hsaving : 0 < γ * τ := by positivity
    exact ⟨not_conjecture52_of_achieves AchievesVHinted.mono (by linarith) (by linarith) hv,
      not_conjecture57_of_achieves AchievesMvHinted.mono (by linarith) (by linarith) hm⟩
  · obtain ⟨γ, hγ, hu⟩ := wordRam_corollary_40_general_times.2 τ₁ τ₂ hpos hlt hτ₂
    have hsaving : 0 < γ * τ₁ := by positivity
    have hτ₂pos : 0 < τ₂ := pos_of_mul_pos_right (hpos.trans hlt) (by linarith)
    have hτ₁ : τ₁ < 1 := by nlinarith
    exact not_conjecture512_of_achieves AchievesUMvHinted.mono (by linarith) (by linarith)
      (by linarith) hu

/-- **Corollary 40**, on the word RAM: the three conjectures fail for `τ < 1/18`, and more
generally for `τ < ε*`. -/
theorem wordRam_corollary_40_fail :
    Items.Corollary_40_fail (1 / 18) ∧ Items.Corollary_40_fail epsStar :=
  ⟨Corollary40.fail_mono (by norm_num) (by linarith [sec4_epsStar_numeric.1])
    Corollary40.fail_general, Corollary40.fail_general⟩

end ThreeSumApsp
