/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Hardy/GoodHeightsW.lean — good heights for the W contour integrand F_𝒵 := L₂ + W′/W
(consumed by Hardy/EFContour.lean; W-analogue of Zeta23/XiPrime/ZeroCount/GoodHeights.lean).

  hardyW_good_heights (hZ : WZerosInStrip t₀) (hs : WSeam t₀) :
    ∃ C > 0, ∃ j₀ ≥ t₀ + 1, ∀ j ≥ j₀, ∃ R ∈ [j, j+1], ∀ s, Im s = ±R → −1 ≤ Re s ≤ 2 →
      W(s) ≠ 0 ∧ ‖L₂(s) + W′/W(s)‖ ≤ C·log²(j+3).

Route: on 1/2 ≤ Re s ≤ 2 this is the GENERIC two-line machine (ZeroCount/Generic.good_heights_two_line) at f := W with
the inputs of Hardy/Count.hardyW_generic_inputs (W analytic on the discs about 2+it, ‖W‖ ≤ C|Im|²,
‖W(2+it)‖ ≥ 1) and the configuration wZeros hZ hs, plus ‖L₂(s)‖ ≤ log(|Im s|+3) + 6 there (Stirling via
ZeroCount.norm_logDeriv_Gammaℝ_le_log, the (1−s)-half shifted by Hardy/TwoLine.logDeriv_Gammaℝ_shift); on
−1 ≤ Re s < 1/2 by the ODD symmetry F_𝒵(1−s) = −F_𝒵(s), which is the logarithmic derivative of the functional
equation W(s) = −χ(s)W(1−s) (χ′/χ = −2L₂, L₂(1−s) = L₂(s)).
-/
import Zeta23.XiPrime.Hardy.Count

open Complex Set Filter Topology Metric
open scoped ComplexConjugate

noncomputable section

namespace Zeta23
namespace XiPrime
namespace Hardy

variable {t₀ : ℝ}

/-! ### ‖L₂‖ ≪ log on 1/2 ≤ Re s ≤ 2 -/

/-- ‖L₂(s)‖ ≤ log(|Im s| + 3) + 6 for 1/2 ≤ Re s ≤ 2, |Im s| ≥ 2. -/
theorem norm_L2_le_log {s : ℂ} (hre : 1 / 2 ≤ s.re) (hre' : s.re ≤ 2) (him : 2 ≤ |s.im|) :
    ‖L2 s‖ ≤ Real.log (|s.im| + 3) + 6 := by
  have hs : s.im ≠ 0 := by intro h; rw [h] at him; norm_num at him
  rw [L2_eq hs]
  have h1 : ‖logDeriv Gammaℝ s‖ ≤ Real.log (|s.im| + 3) + 5 :=
    Zeta23.XiPrime.ZeroCount.norm_logDeriv_Gammaℝ_le_log (by linarith) (by linarith) him
  -- the (1−s)-term: shift to 3 − s
  have hu : (1 - s).im ≠ 0 := im_one_sub_ne_zero hs
  have hshift := logDeriv_Gammaℝ_shift hu
  have e3 : (1 - s) + 2 = 3 - s := by ring
  rw [e3] at hshift
  have h3re : 0 < (3 - s).re := by simp; linarith
  have h3re' : (3 - s).re ≤ 4 := by simp; linarith
  have h3im : 2 ≤ |(3 - s).im| := by simpa using him
  have h2 : ‖logDeriv Gammaℝ (3 - s)‖ ≤ Real.log (|s.im| + 3) + 5 := by
    have := Zeta23.XiPrime.ZeroCount.norm_logDeriv_Gammaℝ_le_log h3re h3re' h3im
    simpa using this
  have hinv : ‖1 / (1 - s)‖ ≤ 1 / 2 := by
    rw [norm_div, norm_one]
    have : 2 ≤ ‖1 - s‖ := by
      have h := Complex.abs_im_le_norm (1 - s)
      simp at h; linarith
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have h2' : ‖logDeriv Gammaℝ (1 - s)‖ ≤ Real.log (|s.im| + 3) + 5 + 1 / 2 := by
    rw [hshift]
    exact (norm_sub_le _ _).trans (add_le_add h2 hinv)
  have hlog : 0 ≤ Real.log (|s.im| + 3) := Real.log_nonneg (by linarith [abs_nonneg s.im])
  calc ‖(logDeriv Gammaℝ s + logDeriv Gammaℝ (1 - s)) / 2‖
      = ‖logDeriv Gammaℝ s + logDeriv Gammaℝ (1 - s)‖ / 2 := by rw [norm_div]; norm_num
    _ ≤ (‖logDeriv Gammaℝ s‖ + ‖logDeriv Gammaℝ (1 - s)‖) / 2 := by gcongr; exact norm_add_le _ _
    _ ≤ Real.log (|s.im| + 3) + 6 := by linarith

/-! ### the odd symmetry of F_𝒵 = L₂ + W′/W -/

/-- logarithmic derivative of W(s) = −χ(s)W(1−s):  W′/W(s) = −2L₂(s) − (W′/W)(1−s)  (off ℝ, W(s) ≠ 0). -/
theorem logDeriv_hardyW_eq_reflect {s : ℂ} (hs : s.im ≠ 0) (hW : hardyW s ≠ 0) :
    logDeriv hardyW s = -2 * L2 s - logDeriv hardyW (1 - s) := by
  have hs' : (1 - s).im ≠ 0 := im_one_sub_ne_zero hs
  have hW' : hardyW (1 - s) ≠ 0 := fun h => hW ((hardyW_one_sub_eq_zero_iff hs).mp h)
  have hχ : chiFE s ≠ 0 := chiFE_ne_zero hs
  -- the functional equation as an identity of functions near s
  have hev : hardyW =ᶠ[𝓝 s] fun z => (-1 : ℂ) * (chiFE z * hardyW (1 - z)) := by
    filter_upwards [isOpen_im_ne_zero.mem_nhds hs] with z hz
    rw [hardyW_eq_neg_chiFE_mul hz]; ring
  have h1 : logDeriv hardyW s = logDeriv (fun z => (-1 : ℂ) * (chiFE z * hardyW (1 - z))) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  have hdχ : DifferentiableAt ℂ chiFE s := (chiFE_analyticAt hs).differentiableAt
  have hdg : DifferentiableAt ℂ (fun z : ℂ => 1 - z) s := by fun_prop
  have hdW1 : DifferentiableAt ℂ (fun z => hardyW (1 - z)) s :=
    (hardyW_differentiableAt hs').comp s hdg
  have h2 : logDeriv (fun z => chiFE z * hardyW (1 - z)) s
      = logDeriv chiFE s + logDeriv (fun z => hardyW (1 - z)) s :=
    logDeriv_mul s hχ hW' hdχ hdW1
  have h3 : logDeriv (fun z => hardyW (1 - z)) s = -logDeriv hardyW (1 - s) := by
    have hc : logDeriv (hardyW ∘ fun z : ℂ => 1 - z) s
        = logDeriv hardyW (1 - s) * deriv (fun z : ℂ => 1 - z) s :=
      logDeriv_comp (hardyW_differentiableAt hs') hdg
    have hd : deriv (fun z : ℂ => 1 - z) s = -1 := by
      rw [deriv_const_sub, deriv_id'']
    have : (hardyW ∘ fun z : ℂ => 1 - z) = fun z => hardyW (1 - z) := rfl
    rw [this] at hc
    rw [hc, hd]; ring
  have hL : logDeriv chiFE s = -2 * L2 s := by
    simp only [L2]; ring
  rw [h1, logDeriv_const_mul s (-1 : ℂ) (by norm_num), h2, h3, hL]
  ring

/-- **F_𝒵(1−s) = −F_𝒵(s)**, F_𝒵 := L₂ + W′/W (off ℝ, at points where W ≠ 0). -/
theorem L2_add_logDeriv_hardyW_one_sub {s : ℂ} (hs : s.im ≠ 0) (hW : hardyW s ≠ 0) :
    L2 (1 - s) + logDeriv hardyW (1 - s) = -(L2 s + logDeriv hardyW s) := by
  rw [logDeriv_hardyW_eq_reflect hs hW, L2_one_sub hs]; ring

/-! ### good heights -/

/-- **Good heights for F_𝒵 = L₂ + W′/W.** -/
theorem hardyW_good_heights (hZ : WZerosInStrip t₀) (hs : WSeam t₀) :
    ∃ C : ℝ, 0 < C ∧ ∃ j₀ : ℕ, t₀ + 1 ≤ j₀ ∧ ∀ j : ℕ, j₀ ≤ j →
    ∃ R : ℝ, (j : ℝ) ≤ R ∧ R ≤ (j : ℝ) + 1 ∧
    ∀ s : ℂ, (s.im = R ∨ s.im = -R) → -1 ≤ s.re → s.re ≤ 2 →
      hardyW s ≠ 0 ∧ ‖L2 s + logDeriv hardyW s‖ ≤ C * (Real.log ((j : ℝ) + 3)) ^ 2 := by
  classical
  obtain ⟨Cf, t₁, hCf, ht₁2, hfa, hgrow, hlow⟩ := hardyW_generic_inputs
  set Zc := wZeros hZ hs with hZc
  set T₀ : ℝ := max t₁ t₀ with hT₀
  have hfa' : ∀ t : ℝ, T₀ ≤ |t| → AnalyticOnNhd ℂ hardyW (closedBall (2 + t * I) (91 / 50)) :=
    fun t ht => hfa t (le_trans (le_max_left _ _) ht)
  have hlow' : ∀ t : ℝ, T₀ ≤ |t| → 1 ≤ ‖hardyW (2 + t * I)‖ :=
    fun t ht => hlow t (le_trans (le_max_left _ _) ht)
  have hlink : ∀ ρ ∈ Zc.carrier, 1 / 2 ≤ ρ.re → hardyW ρ = 0 ∧ analyticOrderNatAt hardyW ρ = Zc.mult ρ :=
    fun ρ hρ _ => ⟨hρ.1.1, rfl⟩
  have hlink' : ∀ ρ : ℂ, 0 < ρ.re → T₀ ≤ |ρ.im| → hardyW ρ = 0 → ρ ∈ Zc.carrier := by
    intro ρ _ hT h0
    have him : ρ.im ≠ 0 := by
      intro h; rw [h, abs_zero] at hT
      linarith [le_trans ht₁2 (le_max_left t₁ t₀)]
    exact ⟨⟨h0, him⟩, le_trans (le_max_right _ _) hT⟩
  obtain ⟨C, hC, j₀, hgh⟩ :=
    Zeta23.XiPrime.ZeroCount.Generic.good_heights_two_line hfa' hCf hgrow hlow' Zc hlink hlink'
  refine ⟨C + 10, by positivity, max (max j₀ 2) (⌈t₀⌉₊ + 1), ?_, fun j hj => ?_⟩
  · have h1 : t₀ ≤ ⌈t₀⌉₊ := Nat.le_ceil t₀
    have h2 : ((⌈t₀⌉₊ + 1 : ℕ) : ℝ) ≤ ((max (max j₀ 2) (⌈t₀⌉₊ + 1) : ℕ) : ℝ) := by
      exact_mod_cast le_max_right _ _
    push_cast at h2 ⊢; linarith
  have hj₀ : j₀ ≤ j := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hj
  have hj2 : (2 : ℝ) ≤ j := by exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hj
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
  -- right half first, with the L₂ term added
  have right : ∀ s : ℂ, (s.im = R ∨ s.im = -R) → 1 / 2 ≤ s.re → s.re ≤ 2 →
      hardyW s ≠ 0 ∧ ‖L2 s + logDeriv hardyW s‖ ≤ (C + 10) * Lg ^ 2 := by
    intro s hsR h1 h2
    obtain ⟨hW, hb⟩ := hright s hsR h1 h2
    have habs : |s.im| = R := by
      rcases hsR with h | h
      · rw [h, abs_of_nonneg (by linarith)]
      · rw [h, abs_neg, abs_of_nonneg (by linarith)]
    have hL2 : ‖L2 s‖ ≤ 2 * Lg + 6 := by
      have := norm_L2_le_log h1 h2 (by rw [habs]; linarith)
      rw [habs] at this; linarith
    refine ⟨hW, (norm_add_le _ _).trans ?_⟩
    have : Lg ≤ Lg ^ 2 := by nlinarith
    nlinarith [hb, hL2]
  intro s hsR hσ1 hσ2
  rcases le_or_gt (1 / 2 : ℝ) s.re with h | h
  · exact right s hsR h hσ2
  · have hsim : s.im ≠ 0 := by
      rcases hsR with h' | h' <;> rw [h'] <;> [skip; rw [neg_ne_zero]] <;> linarith
    have h1 : (1 - s).im = R ∨ (1 - s).im = -R := by
      rcases hsR with h' | h' <;> simp [h']
    obtain ⟨hne, hb⟩ := right (1 - s) h1 (by simp; linarith) (by simp; linarith)
    have hWs : hardyW s ≠ 0 := fun h0 => hne ((hardyW_one_sub_eq_zero_iff hsim).mpr h0)
    refine ⟨hWs, ?_⟩
    rw [L2_add_logDeriv_hardyW_one_sub hsim hWs, norm_neg] at hb
    exact hb

end Hardy
end XiPrime
end Zeta23
