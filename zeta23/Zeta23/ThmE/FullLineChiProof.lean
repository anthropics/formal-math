/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.ThmE.FullLineChi
import Zeta23.WeilEF.FullLine
import Zeta23.ThmE.FoldChi
import Zeta23.ThmE.GammaSideChi
import Zeta23.ThmE.GammaFactsChiProof

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Complex MeasureTheory Real Set Topology Filter DirichletCharacter
open scoped BigOperators ArithmeticFunction

namespace Zeta23
namespace ThmE

open Zeta23.WeilEF

/-! ## ψ growth on the wide strip 1/4 ≤ re ≤ 2 (digamma_growth_strip with the rectangle
widened — needed for ψ((s+κ)/2) with re s ≤ 3/2, κ ≤ 1) -/

theorem digamma_growth_wide : ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1/4 ≤ s.re → s.re ≤ 2 →
    ‖Complex.digamma s‖ ≤ C * Real.log (2 + |s.im|) := by
  -- differentiability of ψ on the right half-plane
  have hdiff : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ Complex.digamma s := by
    intro s hs
    have hzero : ∀ m : ℕ, s ≠ -(m : ℂ) := by
      intro m h
      rw [h] at hs
      simp only [Complex.neg_re, Complex.natCast_re] at hs
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hΓan : AnalyticAt ℂ Complex.Gamma s := by
      rw [Complex.analyticAt_iff_eventually_differentiableAt]
      filter_upwards [hopen.mem_nhds hs] with w hw
      refine Complex.differentiableAt_Gamma w fun m => ?_
      intro h
      rw [h] at hw
      simp only [Complex.neg_re, Complex.natCast_re] at hw
      nlinarith [Nat.cast_nonneg (α := ℝ) m]
    have hΓne : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hzero
    have hψan : AnalyticAt ℂ Complex.digamma s := by
      have h1 : AnalyticAt ℂ (deriv Complex.Gamma) s := hΓan.deriv
      have h2 := h1.div hΓan hΓne
      exact h2.congr (by
        filter_upwards with w
        rw [Complex.digamma_def, logDeriv_apply]
        rfl)
    exact hψan.differentiableAt
  -- bound on the compact rectangle |Im| ≤ 1/2
  have hK : IsCompact (Complex.reProdIm (Set.Icc (1/4 : ℝ) 2) (Set.Icc (-(1/2) : ℝ) (1/2))) :=
    isCompact_Icc.reProdIm isCompact_Icc
  have hcontK : ContinuousOn Complex.digamma
      (Complex.reProdIm (Set.Icc (1/4 : ℝ) 2) (Set.Icc (-(1/2) : ℝ) (1/2))) := by
    intro s hs
    have hsre : 1/4 ≤ s.re := (Complex.mem_reProdIm.mp hs).1.1
    exact ((hdiff s (by linarith)).continuousAt).continuousWithinAt
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcontK
  have hM0 : (0 : ℝ) ≤ M := by
    have h := hM (1/2 : ℂ) (by
      rw [Complex.mem_reProdIm]
      constructor
      · simp only [Complex.div_ofNat_re, Complex.one_re]
        norm_num
      · simp only [Complex.div_ofNat_im, Complex.one_im]
        norm_num)
    exact le_trans (norm_nonneg _) h
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  set K₀ : ℝ := 14 + Real.pi + Real.log 4 with hK₀
  have hK₀0 : (0 : ℝ) < K₀ := by positivity
  refine ⟨max (M / Real.log 2) (1 + K₀ / Real.log 2) + 1, by positivity, fun s hre1 hre2 => ?_⟩
  have hlogmono : Real.log 2 ≤ Real.log (2 + |s.im|) := by
    apply Real.log_le_log (by norm_num)
    have := abs_nonneg s.im
    linarith
  have hlogpos : (0 : ℝ) < Real.log (2 + |s.im|) := lt_of_lt_of_le hlog2 hlogmono
  rcases le_or_gt (|s.im|) (1/2) with him | him
  · -- compact part
    have hsK : s ∈ Complex.reProdIm (Set.Icc (1/4 : ℝ) 2) (Set.Icc (-(1/2) : ℝ) (1/2)) := by
      rw [Complex.mem_reProdIm]
      refine ⟨⟨hre1, hre2⟩, ?_⟩
      rw [Set.mem_Icc]
      constructor <;> [linarith [neg_abs_le s.im]; linarith [le_abs_self s.im]]
    calc ‖Complex.digamma s‖ ≤ M := hM s hsK
      _ = (M / Real.log 2) * Real.log 2 := by
          field_simp
      _ ≤ (max (M / Real.log 2) (1 + K₀ / Real.log 2) + 1) * Real.log (2 + |s.im|) := by
          apply mul_le_mul ?_ hlogmono hlog2.le (by positivity)
          calc M / Real.log 2 ≤ max (M / Real.log 2) (1 + K₀ / Real.log 2) := le_max_left _ _
            _ ≤ max (M / Real.log 2) (1 + K₀ / Real.log 2) + 1 := by linarith
  · -- Stirling part: ‖ψ‖ ≤ ‖ψ − log s + (1/2)/s‖ + ‖log s‖ + ‖(1/2)/s‖
    have hsre0 : (0 : ℝ) < s.re := by linarith
    have hst := Zeta23.StirlingVert.digamma_stirling (w := s) hsre0 (by linarith)
    have hsnorm_lo : (1/4 : ℝ) ≤ ‖s‖ :=
      le_trans hre1 (le_trans (le_abs_self _) (Complex.abs_re_le_norm s))
    have hsnorm0 : (0 : ℝ) < ‖s‖ := by linarith
    have hs0 : s ≠ 0 := by
      intro h
      rw [h, norm_zero] at hsnorm0
      exact lt_irrefl 0 hsnorm0
    have hsnorm_hi : ‖s‖ ≤ 2 + |s.im| := by
      calc ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
        _ ≤ 2 + |s.im| := by
            have : |s.re| ≤ 2 := by
              rw [abs_le]
              constructor <;> linarith
            linarith
    -- ‖log s‖ ≤ |log ‖s‖| + π ≤ (log 4 + log(2+|im|)) + π
    have hlog_s : ‖Complex.log s‖ ≤ |Real.log ‖s‖| + Real.pi := by
      calc ‖Complex.log s‖ ≤ |(Complex.log s).re| + |(Complex.log s).im| :=
            Complex.norm_le_abs_re_add_abs_im _
        _ ≤ |Real.log ‖s‖| + Real.pi := by
            rw [Complex.log_re, Complex.log_im]
            have := Complex.abs_arg_le_pi s
            linarith [abs_nonneg (Complex.arg s)]
    have hlog_abs : |Real.log ‖s‖| ≤ Real.log 4 + Real.log (2 + |s.im|) := by
      rcases le_or_gt (Real.log ‖s‖) 0 with hneg | hpos
      · -- ‖s‖ ≤ 1-ish: |log| = −log ≤ log 4 since ‖s‖ ≥ 1/4
        have h1 : Real.log (1/4 : ℝ) ≤ Real.log ‖s‖ := Real.log_le_log (by norm_num) hsnorm_lo
        have h2 : Real.log (1/4 : ℝ) = -Real.log 4 := by
          rw [show (1/4 : ℝ) = 4⁻¹ by norm_num, Real.log_inv]
        rw [abs_of_nonpos hneg]
        have h3 : (0 : ℝ) ≤ Real.log (2 + |s.im|) := by
          apply Real.log_nonneg
          have := abs_nonneg s.im
          linarith
        linarith
      · rw [abs_of_pos hpos]
        have h1 : Real.log ‖s‖ ≤ Real.log (2 + |s.im|) := by
          apply Real.log_le_log hsnorm0
          have := abs_nonneg s.im
          linarith
        have h2 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
        linarith
    have hinv_s : ‖(1/2 : ℂ) / s‖ ≤ 2 := by
      rw [norm_div]
      have h1 : ‖(1/2 : ℂ)‖ = 1/2 := by
        rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by norm_num, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by norm_num)]
      rw [h1, div_le_iff₀ hsnorm0]
      linarith
    have him2 : 3 / s.im ^ 2 ≤ 12 := by
      have h1 : (1/4 : ℝ) ≤ s.im ^ 2 := by
        have h2 : (1/2 : ℝ) ≤ |s.im| := him.le
        nlinarith [abs_nonneg s.im, sq_abs s.im]
      rw [div_le_iff₀ (by nlinarith)]
      nlinarith
    have htot : ‖Complex.digamma s‖
        ≤ Real.log (2 + |s.im|) + K₀ := by
      have h1 : ‖Complex.digamma s‖
          ≤ ‖Complex.digamma s - Complex.log s + (1/2 : ℂ) / s‖ + ‖Complex.log s‖
            + ‖(1/2 : ℂ) / s‖ := by
        have h2 : Complex.digamma s = (Complex.digamma s - Complex.log s + (1/2 : ℂ) / s)
            + Complex.log s - (1/2 : ℂ) / s := by ring
        calc ‖Complex.digamma s‖
            = ‖(Complex.digamma s - Complex.log s + (1/2 : ℂ) / s)
                + Complex.log s - (1/2 : ℂ) / s‖ := by rw [← h2]
          _ ≤ ‖(Complex.digamma s - Complex.log s + (1/2 : ℂ) / s) + Complex.log s‖
              + ‖(1/2 : ℂ) / s‖ := norm_sub_le _ _
          _ ≤ ‖Complex.digamma s - Complex.log s + (1/2 : ℂ) / s‖ + ‖Complex.log s‖
              + ‖(1/2 : ℂ) / s‖ := by
              have := norm_add_le (Complex.digamma s - Complex.log s + (1/2 : ℂ) / s)
                (Complex.log s)
              linarith
      rw [hK₀]
      have hπ4 : Real.pi < 4 := Real.pi_lt_four
      calc ‖Complex.digamma s‖
          ≤ ‖Complex.digamma s - Complex.log s + (1/2 : ℂ) / s‖ + ‖Complex.log s‖
            + ‖(1/2 : ℂ) / s‖ := h1
        _ ≤ 3 / s.im ^ 2 + (|Real.log ‖s‖| + Real.pi) + 2 := by
            have := hst
            linarith [hlog_s, hinv_s]
        _ ≤ 12 + ((Real.log 4 + Real.log (2 + |s.im|)) + Real.pi) + 2 := by
            linarith [him2, hlog_abs]
        _ ≤ Real.log (2 + |s.im|) + (14 + Real.pi + Real.log 4) := by linarith
    calc ‖Complex.digamma s‖ ≤ Real.log (2 + |s.im|) + K₀ := htot
      _ ≤ Real.log (2 + |s.im|) + (K₀ / Real.log 2) * Real.log (2 + |s.im|) := by
          have h3 : K₀ / Real.log 2 * Real.log 2 ≤ K₀ / Real.log 2 * Real.log (2 + |s.im|) :=
            mul_le_mul_of_nonneg_left hlogmono (by positivity)
          have h4 : K₀ / Real.log 2 * Real.log 2 = K₀ := by field_simp
          linarith
      _ = (1 + K₀ / Real.log 2) * Real.log (2 + |s.im|) := by ring
      _ ≤ (max (M / Real.log 2) (1 + K₀ / Real.log 2) + 1) * Real.log (2 + |s.im|) := by
          apply mul_le_mul_of_nonneg_right ?_ hlogpos.le
          calc (1 + K₀ / Real.log 2) ≤ max (M / Real.log 2) (1 + K₀ / Real.log 2) :=
                le_max_right _ _
            _ ≤ max (M / Real.log 2) (1 + K₀ / Real.log 2) + 1 := by linarith


/-! ## The archimedean log-derivative G_{q,κ} := logDeriv (s ↦ q^{s/2} Γℝ(s+κ)) -/

/-- parity bookkeeping:
gammaFactor χ = Γℝ(· + κ) for κ = 0 (even) or 1 (odd). -/
lemma exists_parity' {N : ℕ} (χ : DirichletCharacter ℂ N) :
    ∃ κ : ℕ, κ ≤ 1 ∧ ∀ s, gammaFactor χ s = Complex.Gammaℝ (s + κ) := by
  rcases χ.even_or_odd with he | ho
  · exact ⟨0, by norm_num, fun s => by rw [he.gammaFactor_def]; norm_num⟩
  · exact ⟨1, le_rfl, fun s => by rw [ho.gammaFactor_def]; norm_num⟩

section Arch

variable (q : ℕ) [NeZero q] (κ : ℕ)

/-- growth of `logDeriv (archChi q κ)` on 1/2 ≤ re ≤ 3/2 (κ ≤ 1). -/
theorem norm_logDeriv_archChi_le (hκ : κ ≤ 1) : ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 3 / 2 →
    ‖logDeriv (archChi q κ) (σ + t * I)‖ ≤ C * Real.log (2 + |t|) := by
  obtain ⟨C, hC, hψ⟩ := digamma_growth_wide
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set A : ℝ := Real.log q / 2 + Real.log Real.pi / 2 with hA
  have hA0 : 0 ≤ A := by
    have h1 : 0 ≤ Real.log q := Real.log_natCast_nonneg q
    have h2 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
    positivity
  refine ⟨A / Real.log 2 + C, by positivity, fun σ t h1 h2 => ?_⟩
  have hre : 0 < ((σ : ℂ) + t * I).re := by simp; linarith
  rw [logDeriv_archChi q κ hre]
  have hκ0 : (0:ℝ) ≤ κ := Nat.cast_nonneg κ
  have hκ1 : (κ:ℝ) ≤ 1 := by exact_mod_cast hκ
  have hw1 : 1 / 4 ≤ ((((σ : ℂ) + t * I) + κ) / 2).re := by simp; linarith
  have hw2 : ((((σ : ℂ) + t * I) + κ) / 2).re ≤ 2 := by simp; linarith
  have hψb := hψ _ hw1 hw2
  have him : |((((σ : ℂ) + t * I) + κ) / 2).im| = |t| / 2 := by simp [abs_div]
  rw [him] at hψb
  have hlogmono : Real.log (2 + |t| / 2) ≤ Real.log (2 + |t|) :=
    Real.log_le_log (by positivity) (by linarith [abs_nonneg t])
  have hlog2le : Real.log 2 ≤ Real.log (2 + |t|) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hlogpos : 0 ≤ Real.log (2 + |t|) := le_trans hlog2.le hlog2le
  have hn1 : ‖(Real.log q : ℂ) / 2‖ = Real.log q / 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_natCast_nonneg q)]
    simp
  have hn2 : ‖-(Real.log Real.pi : ℂ) / 2‖ = Real.log Real.pi / 2 := by
    rw [norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
    simp
  have hn3 : ‖(1/2 : ℂ) * Complex.digamma ((((σ : ℂ) + t * I) + κ) / 2)‖
      ≤ (1/2) * (C * Real.log (2 + |t|)) := by
    rw [norm_mul, show ‖(1/2:ℂ)‖ = 1/2 by norm_num]
    exact mul_le_mul_of_nonneg_left (hψb.trans (mul_le_mul_of_nonneg_left hlogmono hC.le)) (by norm_num)
  calc ‖(Real.log q : ℂ) / 2 + (-(Real.log Real.pi : ℂ) / 2
        + (1/2 : ℂ) * Complex.digamma ((((σ : ℂ) + t * I) + κ) / 2))‖
      ≤ ‖(Real.log q : ℂ) / 2‖ + (‖-(Real.log Real.pi : ℂ) / 2‖
        + ‖(1/2 : ℂ) * Complex.digamma ((((σ : ℂ) + t * I) + κ) / 2)‖) :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_add_le _ _))
    _ ≤ A + C * Real.log (2 + |t|) := by rw [hn1, hn2, hA]; nlinarith
    _ ≤ (A / Real.log 2 + C) * Real.log (2 + |t|) := by
        rw [add_mul]
        have : A ≤ A / Real.log 2 * Real.log (2 + |t|) := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
          exact mul_le_mul_of_nonneg_left hlog2le hA0
        linarith

/-- `logDeriv (archChi q κ)` is complex-differentiable on re > 0. -/
theorem differentiableAt_logDeriv_archChi {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (logDeriv (archChi q κ)) s :=
  (logDeriv_archChi_differentiableOn q κ s hs).differentiableAt (Zeta23.RvM.isOpen_rightHalfPlane.mem_nhds hs)

/-- **the critical-line bracket**: G(1/2+it) + G(1/2−it) = 2π·μ_{κ,q}(t). -/
theorem archChi_bracket (hκ : κ ≤ 1) (hq : 1 ≤ q) (t : ℝ) :
    logDeriv (archChi q κ) (1/2 + t * I) + logDeriv (archChi q κ) (1/2 - t * I)
      = ((2 * Real.pi * muq κ q t : ℝ) : ℂ) := by
  have hp : 0 < ((1:ℂ)/2 + t * I).re := by simp
  have hm : 0 < ((1:ℂ)/2 - t * I).re := by simp
  rw [logDeriv_archChi q κ hp, logDeriv_archChi q κ hm]
  set w : ℂ := ((GammaChi.absc κ : ℝ) : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ) with hw
  have e1 : ((1:ℂ)/2 + t * I + κ) / 2 = w := by
    rw [hw]; unfold GammaChi.absc; push_cast; ring
  have e2 : ((1:ℂ)/2 - t * I + κ) / 2 = starRingEnd ℂ w := by
    have : starRingEnd ℂ w = ((GammaChi.absc κ : ℝ) : ℂ) - Complex.I * ((t / 2 : ℝ) : ℂ) := by
      rw [hw]; simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring
    rw [this]; unfold GammaChi.absc; push_cast; ring
  have hwZ : w ∈ Complex.integerComplement := GammaChi.arg_mem hκ (t / 2)
  rw [e1, e2, Zeta23.WeilEF.digamma_conj hwZ]
  have hre : (1/2 : ℂ) * Complex.digamma w + (1/2 : ℂ) * starRingEnd ℂ (Complex.digamma w)
      = ((Complex.digamma w).re : ℂ) := by
    rw [← mul_add, Complex.add_conj]; push_cast; ring
  have hq0 : (0:ℝ) < q := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hq)
  have hlog : Real.log (q / Real.pi) = Real.log q - Real.log Real.pi :=
    Real.log_div hq0.ne' Real.pi_pos.ne'
  have hμ : 2 * Real.pi * muq κ q t = (Complex.digamma w).re + (Real.log q - Real.log Real.pi) := by
    rw [GammaChi.muq_eq, hlog, ← hw]
    field_simp
  rw [hμ]
  push_cast
  linear_combination hre

end Arch

/-! ## Majorant pack for L(s,χ) and the arch factor -/

section MajorantsChi

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- **L'/L(χ) is bounded on vertical lines to the right of 1** (by Σ Λ(n) n^{−c}). -/
theorem norm_logDeriv_L_le_of_one_lt_re (hχ1 : χ ≠ 1) {c : ℝ} (hc1 : 1 < c) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, ‖logDeriv χ.LFunction ((c : ℂ) + t * I)‖ ≤ M := by
  have hre : ∀ t : ℝ, ((c : ℂ) + t * I).re = c := fun t => by simp
  -- majorant series Σ Λ(n) n^{-c}
  have hs : LSeriesSummable (fun n => (Λ n : ℂ)) (c : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hc1)
  have hns : Summable (fun n : ℕ => ‖LSeries.term (fun n => (Λ n : ℂ)) (c : ℂ) n‖) :=
    summable_norm_iff.mpr hs
  refine ⟨∑' n : ℕ, ‖LSeries.term (fun n => (Λ n : ℂ)) (c : ℂ) n‖,
    tsum_nonneg fun _ => norm_nonneg _, fun t => ?_⟩
  have hre1 : 1 < ((c : ℂ) + t * I).re := by rw [hre]; exact hc1
  have h1 : logDeriv χ.LFunction ((c : ℂ) + t * I)
      = -LSeries (fun n => (χ n : ℂ) * (Λ n : ℂ)) ((c : ℂ) + t * I) := by
    rw [← neg_logDeriv_LFunction_eq hχ1 hre1]; ring
  have hle : ∀ n : ℕ, ‖LSeries.term (fun n => (χ n : ℂ) * (Λ n : ℂ)) ((c : ℂ) + t * I) n‖
      ≤ ‖LSeries.term (fun n => (Λ n : ℂ)) (c : ℂ) n‖ := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, norm_div, norm_div, norm_mul,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), hre, Complex.ofReal_re]
      have hχb := DirichletCharacter.norm_le_one χ (n : ZMod q)
      have hΛ : 0 ≤ ‖((Λ n : ℝ) : ℂ)‖ := norm_nonneg _
      have hrp : (0:ℝ) < (n:ℝ) ^ c := by positivity
      apply div_le_div_of_nonneg_right _ hrp.le
      calc ‖(χ (n : ZMod q) : ℂ)‖ * ‖((Λ n : ℝ) : ℂ)‖ ≤ 1 * ‖((Λ n : ℝ) : ℂ)‖ := by gcongr
        _ = _ := one_mul _
  have hsum' : Summable (fun n : ℕ => ‖LSeries.term (fun n => (χ n : ℂ) * (Λ n : ℂ)) ((c : ℂ) + t * I) n‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hns
  rw [h1, norm_neg, LSeries]
  exact (norm_tsum_le_tsum_norm hsum').trans (Summable.tsum_le_tsum hle hsum' hns)

/-- `t ↦ L'/L(χ)(c+it)` is continuous for c > 1 (χ ≠ 1). -/
theorem continuous_logDeriv_L_line (hχ1 : χ ≠ 1) {c : ℝ} (hc1 : 1 < c) :
    Continuous (fun t : ℝ => logDeriv χ.LFunction ((c : ℂ) + t * I)) := by
  have hline : Continuous (fun t : ℝ => ((c : ℂ) + t * I)) := by fun_prop
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hre1 : 1 < ((c : ℂ) + t * I).re := by simp; linarith
  have hL : χ.LFunction ((c : ℂ) + t * I) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) hre1.le
  have han : AnalyticAt ℂ χ.LFunction ((c : ℂ) + t * I) :=
    (DirichletCharacter.differentiable_LFunction hχ1).analyticAt _
  have : ContinuousAt (fun s => deriv χ.LFunction s / χ.LFunction s) ((c : ℂ) + t * I) :=
    han.deriv.continuousAt.div han.continuousAt hL
  show ContinuousAt ((fun s => deriv χ.LFunction s / χ.LFunction s) ∘ (fun t : ℝ => (c : ℂ) + t * I)) t
  exact ContinuousAt.comp this hline.continuousAt

/-- generic: continuous `φ` with `‖φ t‖ ≤ C/(1+t²)` times `L'/L(χ)(c+it)` is integrable. -/
theorem integrable_mul_logDeriv_L_of_decay (hχ1 : χ ≠ 1) {φ : ℝ → ℂ} (hφc : Continuous φ) {C : ℝ}
    (hφ : ∀ t, ‖φ t‖ ≤ C / (1 + t ^ 2)) {c : ℝ} (hc1 : 1 < c) :
    Integrable (fun t : ℝ => φ t * logDeriv χ.LFunction ((c : ℂ) + t * I)) := by
  obtain ⟨M, hM0, hM⟩ := norm_logDeriv_L_le_of_one_lt_re hχ1 hc1
  have hC0 : 0 ≤ C := by
    have := le_trans (norm_nonneg _) (hφ 0); simpa using this
  refine Integrable.mono' ((integrable_inv_one_add_sq.const_mul (C * M)))
    (hφc.mul (continuous_logDeriv_L_line hχ1 hc1)).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [norm_mul]
  calc ‖φ t‖ * ‖logDeriv χ.LFunction ((c : ℂ) + t * I)‖
      ≤ (C / (1 + t ^ 2)) * M := mul_le_mul (hφ t) (hM t) (norm_nonneg _) (by positivity)
    _ = C * M * (1 + t ^ 2)⁻¹ := by ring

/-- **Integrability of `H(c+it)·L'/L(χ)(c+it)`** on re = c ∈ (1, 3/2] (`hintL`). -/
theorem integrable_Hfn_mul_logDeriv_L (hχ1 : χ ≠ 1) {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3 / 2) :
    Integrable (fun t : ℝ => Hfn k ((c : ℂ) + t * I) * logDeriv χ.LFunction ((c : ℂ) + t * I)) := by
  obtain ⟨C, hC0, hC⟩ := norm_Hfn_le hk hkc
  exact integrable_mul_logDeriv_L_of_decay hχ1 (continuous_Hfn_line hk hkc c)
    (fun t => hC c t (by linarith) (by linarith)) hc1

/-- generic: continuous `φ` with `‖φ t‖ ≤ C/(1+t²)` times `logDeriv (archChi q κ)(σ+it)`,
`1/2 ≤ σ ≤ 3/2`, `κ ≤ 1`, is integrable. -/
theorem integrable_mul_logDeriv_archChi_of_decay (κ : ℕ) (hκ : κ ≤ 1) {φ : ℝ → ℂ}
    (hφc : Continuous φ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ t, ‖φ t‖ ≤ C / (1 + t ^ 2))
    {σ : ℝ} (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 3 / 2) :
    Integrable (fun t : ℝ => φ t * logDeriv (archChi q κ) ((σ : ℂ) + t * I)) := by
  obtain ⟨CG, hCG, hGb⟩ := norm_logDeriv_archChi_le q κ hκ
  set K : ℝ := C * (5 * CG) with hK
  have hmaj : Integrable (fun t : ℝ => K * ((1 : ℝ) + ‖t‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2)) :=
    (integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume)
      (by rw [Module.finrank_self]; norm_num)).const_mul K
  have hGc : Continuous (fun t : ℝ => logDeriv (archChi q κ) ((σ : ℂ) + t * I)) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have hre : 0 < ((σ : ℂ) + t * I).re := by simp; linarith
    show ContinuousAt ((logDeriv (archChi q κ)) ∘ (fun t : ℝ => (σ : ℂ) + t * I)) t
    exact ContinuousAt.comp (differentiableAt_logDeriv_archChi q κ hre).continuousAt
      (by fun_prop : Continuous fun t : ℝ => (σ : ℂ) + t * I).continuousAt
  refine Integrable.mono' hmaj (hφc.mul hGc).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  have hq' : 0 < (1 + t ^ 2 : ℝ) := by positivity
  have hL : ‖logDeriv (archChi q κ) ((σ : ℂ) + t * I)‖ ≤ (5 * CG) * (1 + t ^ 2) ^ (1 / 4 : ℝ) := by
    refine (hGb σ t hσ1 hσ2).trans ?_
    have := log_two_add_le (abs_nonneg t)
    rw [sq_abs] at this
    nlinarith
  rw [norm_mul]
  have hpow : (C / (1 + t ^ 2)) * ((5 * CG) * (1 + t ^ 2) ^ (1 / 4 : ℝ))
      = K * ((1 : ℝ) + ‖t‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2) := by
    rw [Real.norm_eq_abs, sq_abs, hK]
    have e : (1 + t ^ 2 : ℝ) ^ (-(3 / 2 : ℝ) / 2) = (1 + t ^ 2) ^ (1 / 4 : ℝ) / (1 + t ^ 2) := by
      rw [show (-(3 / 2 : ℝ) / 2) = (1 / 4 : ℝ) - 1 by norm_num, Real.rpow_sub hq', Real.rpow_one]
    rw [e]
    field_simp
  calc ‖φ t‖ * ‖logDeriv (archChi q κ) ((σ : ℂ) + t * I)‖
      ≤ (C / (1 + t ^ 2)) * ((5 * CG) * (1 + t ^ 2) ^ (1 / 4 : ℝ)) :=
        mul_le_mul (hC t) hL (norm_nonneg _) (by positivity)
    _ = K * ((1 : ℝ) + ‖t‖ ^ 2) ^ (-(3 / 2 : ℝ) / 2) := hpow

omit [NeZero q] in
/-- gammaFactor in terms of the parity: `gammaFactor χ s = Γℝ(s + parity χ)`. -/
theorem gammaFactor_eq_parity (χ : DirichletCharacter ℂ q) (s : ℂ) :
    gammaFactor χ s = Complex.Gammaℝ (s + parity χ) := by
  unfold parity
  by_cases h : χ.Even
  · rw [h.gammaFactor_def, if_pos h]; norm_num
  · have ho : χ.Odd := (χ.even_or_odd.resolve_left h)
    rw [ho.gammaFactor_def, if_neg h]; norm_num

omit [NeZero q] in
theorem parity_le_one' (χ : DirichletCharacter ℂ q) : parity χ ≤ 1 := by
  unfold parity; split_ifs <;> norm_num

/-- **Λ_sym'/Λ_sym − L'/L = logDeriv (archChi q (parity χ))** on re s > 0, L(s,χ) ≠ 0. -/
theorem logDeriv_completedLSym_sub_L (hq : 1 < q) (hχ1 : χ ≠ 1) {s : ℂ} (hre : 0 < s.re)
    (hL : χ.LFunction s ≠ 0) :
    logDeriv (completedLSym χ) s - logDeriv χ.LFunction s = logDeriv (archChi q (parity χ)) s := by
  rw [logDeriv_completedLSym_split hq hχ1 hre hL]
  have hfun : (fun z => (q : ℂ) ^ (z / 2) * gammaFactor χ z) = archChi q (parity χ) := by
    funext z; rw [gammaFactor_eq_parity]; rfl
  rw [hfun]; ring

/-- the arch difference is the same for χ and χ⁻¹ (equal gammaFactor) — `harchdiff`. -/
theorem logDeriv_completedLSym_sub_L_inv (hq : 1 < q) (hχ1 : χ ≠ 1) (hχ1' : χ⁻¹ ≠ 1) {s : ℂ}
    (hre : 0 < s.re) (hL : χ.LFunction s ≠ 0) (hL' : χ⁻¹.LFunction s ≠ 0) :
    logDeriv (completedLSym χ⁻¹) s - logDeriv χ⁻¹.LFunction s
      = logDeriv (completedLSym χ) s - logDeriv χ.LFunction s := by
  rw [logDeriv_completedLSym_split hq hχ1 hre hL, logDeriv_completedLSym_split hq hχ1' hre hL',
    gammaFactor_inv]
  ring

/-- **Integrability of `(H₁+H₂)·(Λ_sym'/Λ_sym − L'/L)`** on the c-line (`hintΓ`). -/
theorem integrable_Hsum_mul_archDiff (hq : 1 < q) (hχ1 : χ ≠ 1) {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3 / 2) :
    Integrable (fun t : ℝ => (Hfn k ((c : ℂ) + t * I) + Hfn k (1 - c - t * I))
      * (logDeriv (completedLSym χ) ((c : ℂ) + t * I) - logDeriv χ.LFunction ((c : ℂ) + t * I))) := by
  obtain ⟨C, hC0, hC⟩ := norm_Hfn_le hk hkc
  set φ : ℝ → ℂ := fun t => Hfn k ((c : ℂ) + t * I) + Hfn k (1 - c - t * I) with hφ
  have hφc : Continuous φ := by
    refine (continuous_Hfn_line hk hkc c).add ?_
    have h := continuous_Hfn_line hk hkc (1 - c)
    have : (fun t : ℝ => Hfn k (1 - c - t * I))
        = (fun t : ℝ => Hfn k (((1 - c : ℝ) : ℂ) + t * I)) ∘ fun t : ℝ => -t := by
      funext t; simp only [Function.comp_apply, one_sub_cast]
    rw [this]; exact h.comp continuous_neg
  have hφb : ∀ t, ‖φ t‖ ≤ (2 * C) / (1 + t ^ 2) := by
    intro t
    have h1 := hC c t (by linarith) (by linarith)
    have h2 := hC (1 - c) (-t) (by linarith) (by linarith)
    rw [← one_sub_cast, neg_sq] at h2
    calc ‖φ t‖ ≤ ‖Hfn k ((c : ℂ) + t * I)‖ + ‖Hfn k (1 - c - t * I)‖ := norm_add_le _ _
      _ ≤ C / (1 + t ^ 2) + C / (1 + t ^ 2) := add_le_add h1 h2
      _ = (2 * C) / (1 + t ^ 2) := by ring
  have hI := integrable_mul_logDeriv_archChi_of_decay (q := q) (parity χ) (parity_le_one' χ) hφc
    (by positivity) hφb (by linarith : (1:ℝ)/2 ≤ c) hc2
  refine hI.congr (Eventually.of_forall fun t => ?_)
  have hre : 0 < ((c : ℂ) + t * I).re := by simp; linarith
  have hL : χ.LFunction ((c : ℂ) + t * I) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (by simp; linarith)
  simp only [hφ]
  rw [logDeriv_completedLSym_sub_L hq hχ1 hre hL]

end MajorantsChi

/-! ## The archimedean line shift -/

section LineShift

/-- **G-generic archimedean line shift** (gamma_line_shift with Γℝ'/Γℝ replaced by
any `G` holomorphic on re > 0 with ‖G(σ+it)‖ ≤ C_G log(2+|t|) on 1/2 ≤ σ ≤ 3/2). -/
theorem line_shift_generic {G : ℂ → ℂ} (hGd : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ G s)
    (hGgrowth : ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 3 / 2 →
      ‖G (σ + t * I)‖ ≤ C * Real.log (2 + |t|))
    {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3/2) :
    ∫ t : ℝ, (Hfn k (c + t * I) + Hfn k (1 - c - t * I)) * G (c + t * I)
      = ∫ t : ℝ, paperFT k t * (G (1/2 + t * I) + G (1/2 - t * I)) := by
  -- differentiability
  have hHd : Differentiable ℂ (Hfn k) := by
    have h := differentiable_paperFT hk.continuous hkc
    show Differentiable ℂ (fun s => paperFT k ((s - 1/2) / I))
    exact h.comp ((differentiable_id.sub_const _).div_const I)
  set f₁ : ℂ → ℂ := fun s => Hfn k s * G s with hf₁
  set f₂ : ℂ → ℂ := fun s => Hfn k (1 - s) * G s with hf₂
  have hf₁d : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ c → DifferentiableAt ℂ f₁ s := fun s h1 _ =>
    (hHd s).mul (hGd s (by linarith))
  have hf₂d : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ c → DifferentiableAt ℂ f₂ s := fun s h1 _ =>
    ((hHd (1 - s)).comp s ((differentiableAt_const _).sub differentiableAt_id)).mul (hGd s (by linarith))
  -- the majorant
  obtain ⟨Lam₁, hLam₁⟩ := Zeta23.EF.exists_abs_le_of_hasCompactSupport hkc
  set Lam : ℝ := max Lam₁ 0 with hLam
  have hLam0 : 0 ≤ Lam := le_max_right _ _
  have hsupp : ∀ u, k u ≠ 0 → |u| ≤ Lam := fun u hu => (hLam₁ u hu).trans (le_max_left _ _)
  have hki : Integrable k := hk.continuous.integrable_of_hasCompactSupport hkc
  set N : ℝ := (∫ u, ‖k u‖) + ∫ u, ‖deriv (deriv k) u‖ with hN
  have hN0 : 0 ≤ N := add_nonneg (integral_nonneg fun _ => norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _)
  obtain ⟨CG, hCG, hGb⟩ := hGgrowth
  set M : ℝ := 2 * Real.exp Lam * N * CG * 6 with hM
  have hM0 : 0 ≤ M := by positivity
  set φ : ℝ → ℝ := fun t => M * (1 + ‖t‖) ^ (-(3 / 2 : ℝ)) with hφ
  have hφi : Integrable φ := by
    have := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3/2)
      (by rw [Module.finrank_self]; norm_num)).const_mul M
    exact this
  have hφlim : Filter.Tendsto (fun x : ℝ => M * (1 + x) ^ (-(3 / 2 : ℝ))) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun x : ℝ => (1 + x) ^ (-(3 / 2 : ℝ))) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop (by norm_num)).comp (Filter.tendsto_atTop_add_const_left _ 1 Filter.tendsto_id)
    simpa using h1.const_mul M
  have hφtop : Filter.Tendsto φ Filter.atTop (nhds 0) := by
    have : φ = (fun x : ℝ => M * (1 + x) ^ (-(3 / 2 : ℝ))) ∘ (fun t : ℝ => ‖t‖) := by
      funext t; simp [hφ]
    rw [this]
    exact hφlim.comp (by simpa using Filter.tendsto_abs_atTop_atTop)
  have hφbot : Filter.Tendsto φ Filter.atBot (nhds 0) := by
    have : φ = (fun x : ℝ => M * (1 + x) ^ (-(3 / 2 : ℝ))) ∘ (fun t : ℝ => ‖t‖) := by
      funext t; simp [hφ]
    rw [this]
    exact hφlim.comp (by simpa using Filter.tendsto_abs_atBot_atTop)
  -- the key pointwise bound: for |Im z| ≤ 1, ‖paperFT k z‖·‖G(σ+it)‖ ≤ φ t when Re z = ±t
  have hkey : ∀ (σ t : ℝ) (z : ℂ), 1 / 2 ≤ σ → σ ≤ c → |z.im| ≤ 1 → z.re ^ 2 = t ^ 2 →
      ‖paperFT k z‖ * ‖G (σ + t * I)‖ ≤ φ t := by
    intro σ t z h1 h2 hz hzt
    have hH := norm_paperFT_le_uniform hk hki hLam0 hsupp hz
    rw [hzt] at hH
    have hGG := hGb σ t h1 (by linarith)
    have hl := log_two_add_div_le (abs_nonneg t)
    calc ‖paperFT k z‖ * ‖G (σ + t * I)‖
        ≤ (2 * Real.exp Lam * N / (1 + t ^ 2)) * (CG * Real.log (2 + |t|)) :=
          mul_le_mul hH hGG (norm_nonneg _) (by positivity)
      _ = (2 * Real.exp Lam * N * CG) * (Real.log (2 + |t|) / (1 + |t| ^ 2)) := by
          rw [sq_abs]; ring
      _ ≤ (2 * Real.exp Lam * N * CG) * (6 * (1 + |t|) ^ (-(3 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hl (by positivity)
      _ = φ t := by simp only [hφ, hM, Real.norm_eq_abs]; ring
  -- z-bookkeeping for Hfn on the two lines
  have hz₁ : ∀ σ t : ℝ, ((σ : ℂ) + t * I - 1 / 2) / I = (t : ℂ) + ((1 / 2 - σ : ℝ) : ℂ) * I := by
    intro σ t; field_simp; push_cast; ring_nf; simp [I_sq]; ring
  have hz₂ : ∀ σ t : ℝ, ((1 - ((σ : ℂ) + t * I)) - 1 / 2) / I = ((-t : ℝ) : ℂ) + ((σ - 1 / 2 : ℝ) : ℂ) * I := by
    intro σ t; field_simp; push_cast; ring_nf; simp [I_sq]; ring
  have hb₁ : ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ c → ‖f₁ (σ + t * I)‖ ≤ φ t := by
    intro σ t h1 h2
    simp only [hf₁, Hfn, norm_mul]
    rw [hz₁]
    refine hkey σ t _ h1 h2 ?_ ?_
    · simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one, zero_add, add_zero]
      rw [abs_le]; constructor <;> linarith
    · simp
  have hb₂ : ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ c → ‖f₂ (σ + t * I)‖ ≤ φ t := by
    intro σ t h1 h2
    simp only [hf₂, Hfn, norm_mul]
    rw [hz₂]
    refine hkey σ t _ h1 h2 ?_ ?_
    · simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one, zero_add, add_zero]
      rw [abs_le]; constructor <;> linarith
    · simp
  -- shift both lines
  have hab : (1:ℝ) / 2 ≤ c := by linarith
  have hs₁ := vertical_line_shift hab hf₁d hφi hb₁ hφtop hφbot
  have hs₂ := vertical_line_shift hab hf₂d hφi hb₂ hφtop hφbot
  -- integrability on the lines
  have hi₁c : Integrable (fun t : ℝ => f₁ (c + t * I)) :=
    integrable_line (fun t => hf₁d _ (by simp; linarith) (by simp)) hφi (fun t => hb₁ c t hab le_rfl)
  have hi₂c : Integrable (fun t : ℝ => f₂ (c + t * I)) :=
    integrable_line (fun t => hf₂d _ (by simp; linarith) (by simp)) hφi (fun t => hb₂ c t hab le_rfl)
  have hi₁h : Integrable (fun t : ℝ => f₁ ((1/2 : ℝ) + t * I)) :=
    integrable_line (fun t => hf₁d _ (by simp) (by simp; linarith)) hφi (fun t => hb₁ (1/2) t le_rfl hab)
  have hi₂h : Integrable (fun t : ℝ => f₂ ((1/2 : ℝ) + t * I)) :=
    integrable_line (fun t => hf₂d _ (by simp) (by simp; linarith)) hφi (fun t => hb₂ (1/2) t le_rfl hab)
  -- LHS = ∫ f₁(c+it) + ∫ f₂(c+it)
  have hL : ∫ t : ℝ, (Hfn k (c + t * I) + Hfn k (1 - c - t * I)) * G (c + t * I)
      = (∫ t : ℝ, f₁ (c + t * I)) + ∫ t : ℝ, f₂ (c + t * I) := by
    rw [← integral_add hi₁c hi₂c]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hf₁, hf₂]
    rw [show (1 : ℂ) - (↑c + ↑t * I) = 1 - ↑c - ↑t * I by ring]
    ring
  rw [hL, hs₁, hs₂]
  -- evaluate on the critical line
  have e₁ : ∀ t : ℝ, f₁ ((1/2 : ℝ) + t * I) = paperFT k t * G (1/2 + t * I) := by
    intro t
    simp only [hf₁, Hfn]
    congr 2
    · push_cast; field_simp; ring
    · push_cast; ring
  have e₂ : ∀ t : ℝ, f₂ ((1/2 : ℝ) + t * I) = paperFT k (((-t : ℝ) : ℂ)) * G (1/2 + t * I) := by
    intro t
    simp only [hf₂, Hfn]
    congr 2
    · push_cast; field_simp; ring
    · push_cast; ring
  simp_rw [e₁, e₂]
  -- t ↦ −t in the second integral
  have hneg : ∫ t : ℝ, paperFT k (((-t : ℝ) : ℂ)) * G (1/2 + t * I)
      = ∫ t : ℝ, paperFT k t * G (1/2 - t * I) := by
    rw [← integral_neg_eq_self]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [neg_neg]
    push_cast
    ring_nf
  rw [hneg, ← integral_add]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    ring
  · have := hi₁h; simp_rw [e₁] at this; exact this
  · have := hi₂h; simp_rw [e₂] at this
    have h2 := this.comp_neg
    simp only [neg_neg] at h2
    refine (h2.congr (Filter.Eventually.of_forall fun t => ?_))
    push_cast; ring_nf


variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- **gamma_line_shift_chi**: the (Λ_sym'/Λ_sym − L'/L)-part of the
two vertical lines shifts to the critical line where the bracket is 2π·μ_χ. -/
theorem gamma_line_shift_chi' (hq : 1 < q) (hprim : χ.IsPrimitive)
    {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3/2) :
    ∫ t : ℝ, (Hfn k ((c:ℝ) + t * I) + Hfn k (1 - c - t * I))
        * (logDeriv (completedLSym χ) (((c:ℝ):ℂ) + t * I)
          - logDeriv χ.LFunction (((c:ℝ):ℂ) + t * I))
      = ∫ t : ℝ, paperFT k t * ((2 * Real.pi * muq (parity χ) q t : ℝ) : ℂ) := by
  have hχ1 : χ ≠ 1 := ne_one_of_primitive hq hprim
  -- rewrite the integrand as (H₁+H₂)·G, G := logDeriv (archChi q (parity χ))
  have hpt : ∀ t : ℝ, logDeriv (completedLSym χ) (((c:ℝ):ℂ) + t * I)
        - logDeriv χ.LFunction (((c:ℝ):ℂ) + t * I)
      = logDeriv (archChi q (parity χ)) (((c:ℝ):ℂ) + t * I) := by
    intro t
    have hre : 0 < ((((c:ℝ)):ℂ) + t * I).re := by simp; linarith
    exact logDeriv_completedLSym_sub_L hq hχ1 hre
      (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (by simp; linarith))
  simp_rw [hpt]
  rw [line_shift_generic (fun s hs => differentiableAt_logDeriv_archChi q (parity χ) hs)
    (norm_logDeriv_archChi_le q (parity χ) (parity_le_one' χ)) hk hkc hc1 hc2]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  dsimp only
  rw [archChi_bracket q (parity χ) (parity_le_one' χ) hq.le t]

end LineShift

end ThmE
end Zeta23
