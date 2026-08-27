/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmE/MainTermChi.lean — the main term of N_χ(T,2T) (a piece of H-RvM(χ), see
Zeta23/ThmE/RvMChi.lean).
  |N_χ(T,2T) − (T/2π)·ell1q q T| ≤ C log T   (T ≥ T₀; C, T₀ depend on q).
The analogue of the RvM MainTerm.lean assembly for L(s,χ), with Λ_sym = completedLSym
(CountByIntegralChi/FoldChi), Γ/conductor side = gammaSideChi, Backlund for L (BacklundChi),
local count = localCountChi.

The assembly is proved once, q-uniformly (`mainChi_uniform_aux`, absolute constants, log scale
log(q(T+2))); the per-χ headline `mainChi` is its corollary.
-/
import Zeta23.ThmE.LGrowth
import Zeta23.ThmE.Statement
import Zeta23.ThmE.Hypotheses
import Zeta23.ThmE.LocalCountChi
import Zeta23.ThmE.GammaSideChi
import Zeta23.ThmE.CountByIntegralChi
import Zeta23.ThmE.FoldChi
import Zeta23.ThmE.RvMChiDefs
import Zeta23.Assembly
import Zeta23.ThmE.ReZeroCountChi
import Zeta23.ThmE.GammaFactsChiProof

open Complex Set DirichletCharacter MeasureTheory

noncomputable section

namespace Zeta23
namespace ThmE

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-! ### window helpers -/

lemma zerosInL_subset_of_le {a b c d : ℝ} (hca : c ≤ a) (hbd : b ≤ d) :
    zerosInL χ a b ⊆ zerosInL χ c d := by
  rintro ρ ⟨hρ, h1, h2⟩
  exact ⟨hρ, lt_of_le_of_lt hca h1, le_trans h2 hbd⟩

lemma NcountL_le_of_subset (hq : 1 < q) (hprim : χ.IsPrimitive) {a b c d : ℝ}
    (h : zerosInL χ a b ⊆ zerosInL χ c d) : NcountL χ a b ≤ NcountL χ c d := by
  have hs : LSeam χ := LSeam_of hq hprim
  have hsub : (LZeros hs).window a b ⊆ (LZeros hs).window c d := by
    rw [LZeros_window, LZeros_window]
    exact h
  have hmono := (LZeros hs).finsum_mult_mono (T₁ := c) (T₂ := d) hsub subset_rfl
  have e1 := LZeros_N (hs := hs) (T₁ := a) (T₂ := b)
  have e2 := LZeros_N (hs := hs) (T₁ := c) (T₂ := d)
  unfold ZeroConfig.N at e1 e2
  rw [← e1, ← e2]
  exact hmono

lemma NcountL_add (hq : 1 < q) (hprim : χ.IsPrimitive) {T₁ T T₂ : ℝ} (h1 : T₁ ≤ T) (h2 : T ≤ T₂) :
    NcountL χ T₁ T₂ = NcountL χ T₁ T + NcountL χ T T₂ := by
  have hs : LSeam χ := LSeam_of hq hprim
  have := Assembly.N_add (Z := LZeros hs) (a := T₁) (b := T) (c := T₂) h1 h2
  simpa only [LZeros_N] using this

/-- zero-free ordinates for L are dense: every [a, a+1] contains one. -/
lemma exists_goodHeightL (hq : 1 < q) (hprim : χ.IsPrimitive) (a : ℝ) :
    ∃ T ∈ Set.Icc a (a + 1), GoodHeightL χ T := by
  have hs : LSeam χ := LSeam_of hq hprim
  have hfin : (zerosInL χ (a - 1) (a + 2)).Finite := by
    have := (LZeros hs).window_finite (a - 1) (a + 2)
    refine this.subset ?_
    rintro ρ ⟨hρ, h1, h2⟩
    exact ⟨by rwa [LZeros_carrier], h1, h2⟩
  have hSfin : ((fun ρ : ℂ => ρ.im) '' zerosInL χ (a - 1) (a + 2)).Finite := hfin.image _
  have hinf : (Set.Icc a (a + 1)).Infinite := Set.Icc_infinite (by linarith)
  obtain ⟨T, hTd⟩ := (hinf.sdiff hSfin).nonempty
  obtain ⟨hT, hTnot⟩ := hTd
  refine ⟨T, hT, fun ρ hρ him => hTnot ?_⟩
  refine ⟨ρ, ⟨hρ, ?_, ?_⟩, him⟩
  · rw [him]; linarith [hT.1]
  · rw [him]; linarith [hT.2]

/-! ### the split along the half-contour -/

/-- L(σ + iT) ≠ 0 on the horizontal segment [1/2, 2] at a zero-free ordinate. -/
private lemma LFunction_ne_zero_on_segment' (hq : 1 < q) (hprim : χ.IsPrimitive) {T σ : ℝ}
    (hσ : (1/2:ℝ) ≤ σ) (hgood : GoodHeightL χ T) : χ.LFunction ((σ:ℂ) + T * I) ≠ 0 := by
  have hχ1 := ne_one_of_primitive hq hprim
  intro h0
  rcases lt_or_ge σ 1 with hσ1 | hσ1
  · exact hgood _ ⟨h0, by simpa using (by linarith : (0:ℝ) < σ), by simpa using hσ1⟩ (by simp)
  · exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (by simpa using hσ1) h0

/-- continuity of logDeriv L along a segment avoiding zeros (parametrised). -/
lemma continuousOn_logDeriv_LFunction (hχ1 : χ ≠ 1) {S : Set ℂ}
    (hS : ∀ s ∈ S, χ.LFunction s ≠ 0) : ContinuousOn (logDeriv χ.LFunction) S := by
  intro s hs
  apply ContinuousAt.continuousWithinAt
  have hd : DifferentiableAt ℂ χ.LFunction s := differentiable_LFunction hχ1 s
  have hderiv : ContinuousAt (deriv χ.LFunction) s := by
    have : AnalyticAt ℂ χ.LFunction s := (differentiable_LFunction hχ1).analyticAt s
    exact (this.deriv).continuousAt
  exact (hderiv.div (hd.continuousAt) (hS s hs))

set_option maxHeartbeats 800000 in
/-- the half-contour split: logDeriv Λ_sym = logDeriv L + logDeriv arch along L. -/
lemma halfContourChi_split (hq : 1 < q) (hprim : χ.IsPrimitive) {κ : ℕ}
    (hκdef : ∀ s, gammaFactor χ s = Complex.Gammaℝ (s + κ)) {T₁ T₂ : ℝ}
    (_h1 : 1 ≤ T₁) (_h12 : T₁ ≤ T₂) (hg1 : GoodHeightL χ T₁) (hg2 : GoodHeightL χ T₂) :
    RvM.halfContour (logDeriv (completedLSym χ)) T₁ T₂ =
      RvM.halfContour (logDeriv χ.LFunction) T₁ T₂ +
        RvM.halfContour (logDeriv (archChi q κ)) T₁ T₂ := by
  have hχ1 := ne_one_of_primitive hq hprim
  -- pointwise split on Re s ∈ [1/2, 2] with L s ≠ 0
  have hpt : ∀ s : ℂ, (1/2:ℝ) ≤ s.re → 0 < s.re → χ.LFunction s ≠ 0 →
      logDeriv (completedLSym χ) s = logDeriv χ.LFunction s + logDeriv (archChi q κ) s := by
    intro s hσ hσ0 hL
    have h := logDeriv_completedLSym_split hq hχ1 hσ0 hL
    rw [h]
    congr 1
    have : (fun z => (q:ℂ)^(z/2) * gammaFactor χ z) = archChi q κ := by
      funext z
      rw [hκdef z]
      rfl
    rw [this]
  -- segment-wise equality of the three integrals
  have hhor : ∀ T : ℝ, GoodHeightL χ T →
      (∫ σ in (1/2:ℝ)..2, logDeriv (completedLSym χ) ((σ:ℂ) + T * I))
        = (∫ σ in (1/2:ℝ)..2, logDeriv χ.LFunction ((σ:ℂ) + T * I))
          + ∫ σ in (1/2:ℝ)..2, logDeriv (archChi q κ) ((σ:ℂ) + T * I) := by
    intro T hgood
    have hcongr : ∀ σ ∈ Set.uIcc (1/2:ℝ) 2,
        logDeriv (completedLSym χ) ((σ:ℂ) + T * I)
          = logDeriv χ.LFunction ((σ:ℂ) + T * I) + logDeriv (archChi q κ) ((σ:ℂ) + T * I) := by
      intro σ hσ
      rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 2)] at hσ
      exact hpt _ (by simpa using hσ.1) (by simp; linarith [hσ.1])
        (LFunction_ne_zero_on_segment' hq hprim hσ.1 hgood)
    rw [intervalIntegral.integral_congr hcongr]
    apply intervalIntegral.integral_add
    · apply ContinuousOn.intervalIntegrable
      apply (continuousOn_logDeriv_LFunction hχ1 (S := {s : ℂ | (1/2:ℝ) ≤ s.re ∧ s.im = T ∧
          χ.LFunction s ≠ 0}) (fun s hs => hs.2.2)).comp (by fun_prop : Continuous fun σ : ℝ =>
          (σ:ℂ) + T * I).continuousOn ?_
      intro σ hσ
      rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 2)] at hσ
      exact ⟨by simpa using hσ.1, by simp, LFunction_ne_zero_on_segment' hq hprim hσ.1 hgood⟩
    · apply ContinuousOn.intervalIntegrable
      apply ((logDeriv_archChi_differentiableOn q κ).continuousOn.comp
        (by fun_prop : Continuous fun σ : ℝ => (σ:ℂ) + T * I).continuousOn ?_)
      intro σ hσ
      rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 2)] at hσ
      show (0:ℝ) < ((σ:ℂ) + T * I).re
      simp
      linarith [hσ.1]
  have hvert :
      (∫ t in T₁..T₂, logDeriv (completedLSym χ) ((2:ℂ) + t * I))
        = (∫ t in T₁..T₂, logDeriv χ.LFunction ((2:ℂ) + t * I))
          + ∫ t in T₁..T₂, logDeriv (archChi q κ) ((2:ℂ) + t * I) := by
    have hcongr : ∀ t ∈ Set.uIcc T₁ T₂,
        logDeriv (completedLSym χ) ((2:ℂ) + t * I)
          = logDeriv χ.LFunction ((2:ℂ) + t * I) + logDeriv (archChi q κ) ((2:ℂ) + t * I) := by
      intro t ht
      have hre2 : ((2:ℂ) + t * I).re = 2 := by simp
      exact hpt _ (by rw [hre2]; norm_num) (by rw [hre2]; norm_num)
        (LFunction_ne_zero_of_two_le_re (by rw [hre2]))
    rw [intervalIntegral.integral_congr hcongr]
    apply intervalIntegral.integral_add
    · apply ContinuousOn.intervalIntegrable
      apply (continuousOn_logDeriv_LFunction hχ1 (S := {s : ℂ | s.re = 2})
        (fun s hs => LFunction_ne_zero_of_two_le_re (by rw [hs]))).comp
        (by fun_prop : Continuous fun t : ℝ => (2:ℂ) + t * I).continuousOn ?_
      intro t ht
      show ((2:ℂ) + t * I).re = 2
      simp
    · apply ContinuousOn.intervalIntegrable
      apply ((logDeriv_archChi_differentiableOn q κ).continuousOn.comp
        (by fun_prop : Continuous fun t : ℝ => (2:ℂ) + t * I).continuousOn ?_)
      intro t ht
      show (0:ℝ) < ((2:ℂ) + t * I).re
      simp
  unfold RvM.halfContour
  rw [hhor T₁ hg1, hhor T₂ hg2, hvert]
  ring

/-! ### The q-UNIFORM assembly (absolute constants) -/

/-- q-uniform |μ_χ| ≤ (C+2)·log(q(τ+3)) for τ ≥ 1, from the bounded Stirling field. -/
theorem muq_le_log_uniform {κ q : ℕ} [NeZero q] {C : ℝ} (hC : 0 ≤ C)
    (hst : ∀ τ : ℝ, 1 ≤ |τ| →
      |muq κ q τ - (1 / (2 * Real.pi)) * Real.log (q * |τ| / (2 * Real.pi))| ≤ C / τ ^ 2)
    (hq1 : 1 ≤ q) : ∀ τ : ℝ, 1 ≤ τ →
    |muq κ q τ| ≤ (C + 2) * Real.log ((q:ℝ) * (τ + 3)) := by
  intro τ hτ
  have hτ0 : (0:ℝ) < τ := by linarith
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hq1' : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
  have h1 := hst τ (by rw [abs_of_pos hτ0]; exact hτ)
  rw [abs_of_pos hτ0] at h1
  obtain ⟨hl, hr⟩ := abs_le.mp h1
  set L : ℝ := Real.log ((q:ℝ) * (τ + 3)) with hLdef
  have hqt4 : (4:ℝ) ≤ (q:ℝ) * (τ + 3) := by nlinarith
  have hL1 : 1 ≤ L := by
    rw [hLdef, ← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith
  -- 0 ≤ log(qτ/2π) ≤ L   and   C/τ² ≤ C
  have harg : Real.log ((q:ℝ) * τ / (2 * Real.pi)) ≤ L := by
    rw [hLdef]
    apply Real.log_le_log (by positivity)
    have hπ3 := Real.pi_gt_three
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hCτ : |C / τ ^ 2| ≤ C := by
    rw [abs_div, abs_of_nonneg hC, abs_of_pos (by positivity : (0:ℝ) < τ ^ 2)]
    apply div_le_self hC (by nlinarith)
  obtain ⟨hCl, hCr⟩ := abs_le.mp hCτ
  have h2π0 : 0 < 1 / (2 * Real.pi) := by positivity
  have h2π1 : 1 / (2 * Real.pi) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
  -- lower bound for log(qτ/2π): ≥ −log(2π) ≥ −2 ≥ −2L  (qτ ≥ 1·1 = 1 ⇒ log ≥ −log 2π)
  have hlow : -(2 * L) ≤ 1 / (2 * Real.pi) * Real.log ((q:ℝ) * τ / (2 * Real.pi)) := by
    have h7 : Real.log ((q:ℝ) * τ / (2 * Real.pi)) ≥ -Real.log (2 * Real.pi) := by
      rw [Real.log_div (by positivity) (by positivity)]
      have : 0 ≤ Real.log ((q:ℝ) * τ) := Real.log_nonneg (by nlinarith)
      linarith
    have h8 : Real.log (2 * Real.pi) ≤ 2 * L := by
      have h9 : Real.log (2 * Real.pi) ≤ Real.log 16 := by
        apply Real.log_le_log (by positivity)
        nlinarith [Real.pi_lt_d2]
      have h10 : Real.log 16 = 2 * Real.log 4 := by
        rw [show (16:ℝ) = 4^2 by norm_num, Real.log_pow]; push_cast; ring
      have h11 : Real.log 4 ≤ L := by
        rw [hLdef]; exact Real.log_le_log (by norm_num) hqt4
      linarith
    have hln2π0 : 0 ≤ Real.log (2 * Real.pi) :=
      Real.log_nonneg (by nlinarith [Real.pi_gt_three])
    have h12 := mul_le_mul_of_nonneg_left h7 h2π0.le
    -- h12 : (1/2π)·(−log 2π) ≤ (1/2π)·log(qτ/2π)
    have h13 : -(2 * L) ≤ 1 / (2 * Real.pi) * -(Real.log (2 * Real.pi)) := by
      have h14 : 1 / (2 * Real.pi) * Real.log (2 * Real.pi) ≤ 1 * (2 * L) := by
        apply mul_le_mul h2π1 h8 hln2π0 (by norm_num)
      nlinarith
    linarith
  rw [abs_le]
  constructor
  · have : 1 / (2 * Real.pi) * Real.log ((q:ℝ) * τ / (2 * Real.pi)) - C ≤ muq κ q τ := by linarith
    nlinarith
  · have hup : 1 / (2 * Real.pi) * Real.log ((q:ℝ) * τ / (2 * Real.pi)) ≤ L := by
      rcases le_or_gt 0 (Real.log ((q:ℝ) * τ / (2 * Real.pi))) with h | h
      · calc 1 / (2 * Real.pi) * Real.log ((q:ℝ) * τ / (2 * Real.pi))
            ≤ 1 * Real.log ((q:ℝ) * τ / (2 * Real.pi)) := mul_le_mul_of_nonneg_right h2π1 h
          _ = Real.log ((q:ℝ) * τ / (2 * Real.pi)) := one_mul _
          _ ≤ L := harg
      · nlinarith
    nlinarith

set_option maxHeartbeats 3200000 in
/-- q-uniform main-term assembly, parametric in the uniform Backlund and H-Γ(χ)-bounded inputs
(shapes = RvMChiUniform's backlund_horizontalChi_uniform / gammaFactsChi_uniform). -/
theorem mainChi_uniform_aux
    (hBack : ∃ C : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ T : ℝ, (∀ ρ, IsNontrivialZeroL χ ρ → ρ.im ≠ T) →
        |(∫ σ in (1 / 2 : ℝ)..2, logDeriv χ.LFunction (σ + T * I)).im|
          ≤ C * Real.log (q * (|T| + 3)))
    (hΓ : ∃ C : ℝ, ∀ (κ q : ℕ), κ ≤ 1 → 1 ≤ q → GammaFactsChiBounded κ q C) :
    ∃ A T₀ : ℝ, 0 < A ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q → χ.IsPrimitive →
    ∀ T : ℝ, T₀ ≤ T →
      |(NcountL χ T (2 * T) : ℝ) - T / (2 * Real.pi) * ell1q q T|
        ≤ A * Real.log (q * (T + 2)) := by
  obtain ⟨CB, hB⟩ := hBack
  obtain ⟨CΓ, hΓall⟩ := hΓ
  obtain ⟨A₀, hA₀1, hA₀⟩ := localCountChi_uniform_proof
  have hA₀0 : 0 ≤ A₀ := by linarith
  set CM : ℝ := |CΓ| + 2 with hCM
  have hCM0 : 0 < CM := by positivity
  refine ⟨4 * |CB| + 4 + 8 * A₀ + 8 * CM + |CΓ|, max 4 (|CΓ| + 1),
    by positivity, ?_⟩
  intro q _ χ hq1 hprim T hT
  have hχ1 : χ ≠ 1 := ne_one_of_primitive hq1 hprim
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hq2 : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq1
  have hqnat1 : 1 ≤ q := hq1.le
  have hT4 : 4 ≤ T := le_trans (le_max_left _ _) hT
  have hTΓ : |CΓ| + 1 ≤ T := le_trans (le_max_right _ _) hT
  -- parity
  obtain ⟨κ, hκ1, hκdef⟩ : ∃ κ : ℕ, κ ≤ 1 ∧
      ∀ s, gammaFactor χ s = Complex.Gammaℝ (s + κ) := by
    rcases χ.even_or_odd with he | ho
    · exact ⟨0, by norm_num, fun s => by rw [he.gammaFactor_def]; norm_num⟩
    · exact ⟨1, le_rfl, fun s => by rw [ho.gammaFactor_def]; norm_num⟩
  have hΓb := hΓall κ q hκ1 hqnat1
  -- log scale
  set L' : ℝ := Real.log ((q:ℝ) * (T + 2)) with hL'def
  have hqT12 : (12:ℝ) ≤ (q:ℝ) * (T + 2) := by nlinarith
  have hL'1 : 1 ≤ L' := by
    rw [hL'def, ← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith
  have hL'0 : 0 < L' := by linarith
  -- generic: log(q·x) ≤ 2L' whenever 0 < x ≤ (T+2)²·q  (used at x = |T₁|+3 etc.)
  have hlog2L : ∀ x : ℝ, 0 < x → (q:ℝ) * x ≤ ((q:ℝ) * (T + 2))^2 → Real.log ((q:ℝ) * x) ≤ 2 * L' := by
    intro x hx hxq
    have h1 : Real.log ((q:ℝ) * x) ≤ Real.log (((q:ℝ) * (T + 2))^2) :=
      Real.log_le_log (by positivity) hxq
    have h2 : Real.log (((q:ℝ) * (T + 2))^2) = 2 * L' := by
      rw [hL'def, Real.log_pow]; push_cast; ring
    linarith
  -- good heights
  obtain ⟨T₁, hT₁mem, hg1⟩ := exists_goodHeightL hq1 hprim (T - 1)
  obtain ⟨T₂, hT₂mem, hg2⟩ := exists_goodHeightL hq1 hprim (2 * T)
  have hT₁a : T - 1 ≤ T₁ := hT₁mem.1
  have hT₁b : T₁ ≤ T := by have := hT₁mem.2; linarith
  have hT₂a : 2 * T ≤ T₂ := hT₂mem.1
  have hT₂b : T₂ ≤ 2 * T + 1 := hT₂mem.2
  have h1T₁ : 1 ≤ T₁ := by linarith
  have h12 : T₁ ≤ T₂ := by linarith
  have hN := NcountL_eq_im_halfContour hq1 hprim h12 hg1 hg2
  have hsplit := halfContourChi_split hq1 hprim hκdef h1T₁ h12 hg1 hg2
  have hgam := gammaSideChi q κ (T₁ := T₁) (T₂ := T₂) (by linarith) (by linarith)
  have hadd : (NcountL χ T₁ T₂ : ℝ)
      = (NcountL χ T₁ T : ℝ) + (NcountL χ T (2*T) : ℝ) + (NcountL χ (2*T) T₂ : ℝ) := by
    have e1 := NcountL_add hq1 hprim (T₁ := T₁) (T := T) (T₂ := T₂) hT₁b (by linarith)
    have e2 := NcountL_add hq1 hprim (T₁ := T) (T := 2*T) (T₂ := T₂) (by linarith) hT₂a
    rw [e1, e2]; push_cast; ring
  -- end windows ≤ 2A₀L' each... (uniform local count at T₁ resp. 2T)
  have hw1 : (NcountL χ T₁ T : ℝ) ≤ 2 * A₀ * L' := by
    have hsub : NcountL χ T₁ T ≤ NcountL χ T₁ (T₁ + 1) :=
      NcountL_le_of_subset hq1 hprim (zerosInL_subset_of_le le_rfl (by linarith))
    calc (NcountL χ T₁ T : ℝ) ≤ (NcountL χ T₁ (T₁ + 1) : ℝ) := by exact_mod_cast hsub
      _ ≤ A₀ * Real.log ((q:ℝ) * (|T₁| + 3)) := hA₀ q χ hq1 hprim T₁
      _ ≤ A₀ * (2 * L') := by
          refine mul_le_mul_of_nonneg_left ?_ hA₀0
          apply hlog2L _ (by positivity)
          rw [abs_of_pos (by linarith : (0:ℝ) < T₁)]
          nlinarith
      _ = 2 * A₀ * L' := by ring
  have hw2 : (NcountL χ (2*T) T₂ : ℝ) ≤ 2 * A₀ * L' := by
    have hsub : NcountL χ (2*T) T₂ ≤ NcountL χ (2*T) (2*T + 1) :=
      NcountL_le_of_subset hq1 hprim (zerosInL_subset_of_le le_rfl hT₂b)
    calc (NcountL χ (2*T) T₂ : ℝ) ≤ (NcountL χ (2*T) (2*T+1) : ℝ) := by exact_mod_cast hsub
      _ ≤ A₀ * Real.log ((q:ℝ) * (|2*T| + 3)) := hA₀ q χ hq1 hprim (2*T)
      _ ≤ A₀ * (2 * L') := by
          refine mul_le_mul_of_nonneg_left ?_ hA₀0
          apply hlog2L _ (by positivity)
          rw [abs_of_pos (by linarith : (0:ℝ) < 2*T)]
          nlinarith
      _ = 2 * A₀ * L' := by ring
  -- Backlund on the horizontals + π on the vertical
  have habs₁ : |T₁| = T₁ := abs_of_pos (by linarith)
  have habs₂ : |T₂| = T₂ := abs_of_pos (by linarith)
  have hbk1 := hB q χ hχ1 T₁ hg1
  have hbk2 := hB q χ hχ1 T₂ hg2
  rw [habs₁] at hbk1
  rw [habs₂] at hbk2
  have hlogqT₁ : Real.log ((q:ℝ) * (T₁ + 3)) ≤ 2 * L' :=
    hlog2L _ (by linarith) (by nlinarith)
  have hlogqT₂ : Real.log ((q:ℝ) * (T₂ + 3)) ≤ 2 * L' :=
    hlog2L _ (by linarith) (by nlinarith)
  have hbk1' : |(∫ σ in (1/2:ℝ)..2, logDeriv χ.LFunction (σ + T₁ * I)).im| ≤ |CB| * (2 * L') := by
    refine hbk1.trans (le_trans (mul_le_mul (le_abs_self CB) hlogqT₁ ?_ (abs_nonneg _)) le_rfl)
    have : (0:ℝ) < (q:ℝ) * (T₁ + 3) := by positivity
    rw [← Real.log_one]
    exact Real.log_le_log one_pos (by nlinarith)
  have hbk2' : |(∫ σ in (1/2:ℝ)..2, logDeriv χ.LFunction (σ + T₂ * I)).im| ≤ |CB| * (2 * L') := by
    refine hbk2.trans (le_trans (mul_le_mul (le_abs_self CB) hlogqT₂ ?_ (abs_nonneg _)) le_rfl)
    rw [← Real.log_one]
    exact Real.log_le_log one_pos (by nlinarith)
  have hvert := vertical_twoChi hχ1 T₁ T₂
  have hLbound : |(RvM.halfContour (logDeriv χ.LFunction) T₁ T₂).im|
      ≤ |CB| * (2 * L') + Real.pi + |CB| * (2 * L') := by
    unfold RvM.halfContour
    have eim : ((∫ σ in (1/2:ℝ)..2, logDeriv χ.LFunction (σ + T₁ * I))
        + (∫ t in T₁..T₂, logDeriv χ.LFunction (2 + t * I)) * I
        - ∫ σ in (1/2:ℝ)..2, logDeriv χ.LFunction (σ + T₂ * I)).im
        = (∫ σ in (1/2:ℝ)..2, logDeriv χ.LFunction (σ + T₁ * I)).im
          + ((∫ t in T₁..T₂, logDeriv χ.LFunction (2 + t * I)) * I).im
          - (∫ σ in (1/2:ℝ)..2, logDeriv χ.LFunction (σ + T₂ * I)).im := by
      simp [Complex.add_im, Complex.sub_im]
    rw [eim]
    have hmulI : ((∫ t in T₁..T₂, logDeriv χ.LFunction (2 + t * I)) * I).im
        = (∫ t in T₁..T₂, logDeriv χ.LFunction (2 + t * I) * I).im :=
      congrArg Complex.im (intervalIntegral.integral_mul_const (μ := MeasureTheory.volume) I
        (fun t : ℝ => logDeriv χ.LFunction (2 + t * I))).symm
    calc |(∫ σ in (1/2:ℝ)..2, logDeriv χ.LFunction (σ + T₁ * I)).im
          + ((∫ t in T₁..T₂, logDeriv χ.LFunction (2 + t * I)) * I).im
          - (∫ σ in (1/2:ℝ)..2, logDeriv χ.LFunction (σ + T₂ * I)).im|
        ≤ |(∫ σ in (1/2:ℝ)..2, logDeriv χ.LFunction (σ + T₁ * I)).im|
          + |((∫ t in T₁..T₂, logDeriv χ.LFunction (2 + t * I)) * I).im|
          + |(∫ σ in (1/2:ℝ)..2, logDeriv χ.LFunction (σ + T₂ * I)).im| :=
          (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ |CB| * (2 * L') + Real.pi + |CB| * (2 * L') := by
          rw [hmulI]
          linarith [hvert]
  -- μ_χ bookkeeping (bounded Γ-facts)
  have hμc : Continuous (muq κ q) := hΓb.smooth.continuous
  have hCMbound := muq_le_log_uniform (abs_nonneg CΓ)
    (fun τ hτ => (hΓb.stirling τ hτ).trans (by
      have : CΓ / τ ^ 2 ≤ |CΓ| / τ ^ 2 := by
        gcongr
        exact le_abs_self _
      linarith)) hqnat1
  have hμint : ∀ a b : ℝ, IntervalIntegrable (muq κ q) MeasureTheory.volume a b :=
    fun a b => hμc.intervalIntegrable a b
  have hμsplit : (∫ t in T₁..T₂, muq κ q t)
      = (∫ t in T₁..T, muq κ q t) + (∫ t in T..(2*T), muq κ q t)
        + ∫ t in (2*T)..T₂, muq κ q t := by
    have e1 : (∫ t in T₁..(2*T), muq κ q t)
        = (∫ t in T₁..T, muq κ q t) + ∫ t in T..(2*T), muq κ q t :=
      (intervalIntegral.integral_add_adjacent_intervals (hμint T₁ T) (hμint T (2*T))).symm
    have e2 : (∫ t in T₁..T₂, muq κ q t)
        = (∫ t in T₁..(2*T), muq κ q t) + ∫ t in (2*T)..T₂, muq κ q t :=
      (intervalIntegral.integral_add_adjacent_intervals (hμint T₁ (2*T)) (hμint (2*T) T₂)).symm
    rw [e2, e1]
  have hμwin : ∀ a b : ℝ, 1 ≤ a → a ≤ b → b ≤ 2*T + 1 → |b - a| ≤ 1 →
      |∫ t in a..b, muq κ q t| ≤ 2 * CM * L' := by
    intro a b ha hab hb hba
    have hbound : ∀ t ∈ Set.uIoc a b, ‖muq κ q t‖ ≤ CM * (2 * L') := by
      intro t ht
      rw [Set.uIoc_of_le hab] at ht
      have ht1 : 1 ≤ t := le_trans ha ht.1.le
      have ht2 : t ≤ 2*T + 1 := le_trans ht.2 hb
      rw [Real.norm_eq_abs]
      refine (hCMbound t ht1).trans ?_
      have h1 : Real.log ((q:ℝ) * (t + 3)) ≤ 2 * L' :=
        hlog2L _ (by linarith) (by nlinarith)
      calc (|CΓ| + 2) * Real.log ((q:ℝ) * (t + 3)) ≤ (|CΓ| + 2) * (2 * L') := by
            apply mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = CM * (2 * L') := by rw [hCM]
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [Real.norm_eq_abs] at hnorm
    calc |∫ t in a..b, muq κ q t| ≤ CM * (2 * L') * |b - a| := hnorm
      _ ≤ CM * (2 * L') * 1 := by
          apply mul_le_mul_of_nonneg_left hba (by positivity)
      _ = 2 * CM * L' := by ring
  have hμ1 : |∫ t in T₁..T, muq κ q t| ≤ 2 * CM * L' :=
    hμwin T₁ T h1T₁ hT₁b (by linarith) (by rw [abs_of_nonneg (by linarith)]; linarith)
  have hμ2 : |∫ t in (2*T)..T₂, muq κ q t| ≤ 2 * CM * L' :=
    hμwin (2*T) T₂ (by linarith) hT₂a (by linarith) (by rw [abs_of_nonneg (by linarith)]; linarith)
  have hintmu := hΓb.int_mu T (by linarith [le_abs_self CΓ])
  have hCΓT : CΓ / T ≤ |CΓ| := by
    calc CΓ / T ≤ |CΓ| / T := by gcongr; exact le_abs_self _
      _ ≤ |CΓ| / 1 := by
          apply div_le_div_of_nonneg_left (abs_nonneg _) one_pos
          linarith
      _ = |CΓ| := div_one _
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hkey : (NcountL χ T (2*T) : ℝ) - T / (2 * Real.pi) * ell1q q T
      = (1/Real.pi) * (RvM.halfContour (logDeriv χ.LFunction) T₁ T₂).im
        + ((∫ t in T₁..T, muq κ q t) + (∫ t in (2*T)..T₂, muq κ q t)
        + ((∫ t in T..(2*T), muq κ q t) - T * ell1q q T / (2 * Real.pi)))
        - ((NcountL χ T₁ T : ℝ) + (NcountL χ (2*T) T₂ : ℝ)) := by
    have hΛim : (1/Real.pi) * (RvM.halfContour (logDeriv (completedLSym χ)) T₁ T₂).im
        = (1/Real.pi) * (RvM.halfContour (logDeriv χ.LFunction) T₁ T₂).im
          + (1/Real.pi) * (RvM.halfContour (logDeriv (archChi q κ)) T₁ T₂).im := by
      rw [hsplit, Complex.add_im]; ring
    have h5 : (NcountL χ T₁ T₂ : ℝ)
        = (1/Real.pi) * (RvM.halfContour (logDeriv χ.LFunction) T₁ T₂).im
          + ∫ t in T₁..T₂, muq κ q t := by
      rw [hN, hΛim, hgam]
    rw [hμsplit] at h5
    have hTell : T / (2 * Real.pi) * ell1q q T = T * ell1q q T / (2 * Real.pi) := by ring
    rw [hTell]
    linarith [hadd]
  have hA : |(1/Real.pi) * (RvM.halfContour (logDeriv χ.LFunction) T₁ T₂).im|
      ≤ (4 * |CB| + 4) * L' := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1/Real.pi)]
    have hπ1 : (1:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hfrac : (1:ℝ)/Real.pi ≤ 1 := by rw [div_le_one hπ]; exact hπ1
    have step : (1/Real.pi) * |(RvM.halfContour (logDeriv χ.LFunction) T₁ T₂).im|
        ≤ |CB| * (2 * L') + Real.pi + |CB| * (2 * L') := by
      calc (1/Real.pi) * |(RvM.halfContour (logDeriv χ.LFunction) T₁ T₂).im|
          ≤ 1 * |(RvM.halfContour (logDeriv χ.LFunction) T₁ T₂).im| :=
            mul_le_mul_of_nonneg_right hfrac (abs_nonneg _)
        _ = |(RvM.halfContour (logDeriv χ.LFunction) T₁ T₂).im| := one_mul _
        _ ≤ |CB| * (2 * L') + Real.pi + |CB| * (2 * L') := hLbound
    have hπ4 : Real.pi ≤ 4 * L' := by nlinarith [Real.pi_lt_d2]
    nlinarith [abs_nonneg CB]
  have hmid : |(∫ t in T..(2*T), muq κ q t) - T * ell1q q T / (2 * Real.pi)| ≤ |CΓ| * L' := by
    calc |(∫ t in T..(2*T), muq κ q t) - T * ell1q q T / (2 * Real.pi)| ≤ CΓ / T := hintmu
      _ ≤ |CΓ| := hCΓT
      _ ≤ |CΓ| * L' := le_mul_of_one_le_right (abs_nonneg _) hL'1
  rw [hkey]
  have htri : |(1/Real.pi) * (RvM.halfContour (logDeriv χ.LFunction) T₁ T₂).im
        + ((∫ t in T₁..T, muq κ q t) + (∫ t in (2*T)..T₂, muq κ q t)
        + ((∫ t in T..(2*T), muq κ q t) - T * ell1q q T / (2 * Real.pi)))
        - ((NcountL χ T₁ T : ℝ) + (NcountL χ (2*T) T₂ : ℝ))|
      ≤ |(1/Real.pi) * (RvM.halfContour (logDeriv χ.LFunction) T₁ T₂).im|
        + (|∫ t in T₁..T, muq κ q t| + |∫ t in (2*T)..T₂, muq κ q t|
        + |(∫ t in T..(2*T), muq κ q t) - T * ell1q q T / (2 * Real.pi)|)
        + ((NcountL χ T₁ T : ℝ) + (NcountL χ (2*T) T₂ : ℝ)) := by
    have h2 := abs_add_le (∫ t in T₁..T, muq κ q t) (∫ t in (2*T)..T₂, muq κ q t)
    have h3 := abs_add_le ((∫ t in T₁..T, muq κ q t) + (∫ t in (2*T)..T₂, muq κ q t))
      ((∫ t in T..(2*T), muq κ q t) - T * ell1q q T / (2 * Real.pi))
    have h1 := abs_add_le ((1/Real.pi) * (RvM.halfContour (logDeriv χ.LFunction) T₁ T₂).im)
      ((∫ t in T₁..T, muq κ q t) + (∫ t in (2*T)..T₂, muq κ q t)
        + ((∫ t in T..(2*T), muq κ q t) - T * ell1q q T / (2 * Real.pi)))
    have h4 := abs_sub (((1/Real.pi) * (RvM.halfContour (logDeriv χ.LFunction) T₁ T₂).im)
        + ((∫ t in T₁..T, muq κ q t) + (∫ t in (2*T)..T₂, muq κ q t)
        + ((∫ t in T..(2*T), muq κ q t) - T * ell1q q T / (2 * Real.pi))))
      ((NcountL χ T₁ T : ℝ) + (NcountL χ (2*T) T₂ : ℝ))
    have h5 : |(NcountL χ T₁ T : ℝ) + (NcountL χ (2*T) T₂ : ℝ)|
        = (NcountL χ T₁ T : ℝ) + (NcountL χ (2*T) T₂ : ℝ) := abs_of_nonneg (by positivity)
    rw [h5] at h4
    linarith
  refine htri.trans ?_
  nlinarith [hA, hμ1, hμ2, hmid, hw1, hw2, hL'0]


/-! ### Per-χ main term (from the q-uniform assembly) -/

/-- **Main term for N_χ(T,2T)** (per-χ constant; from `mainChi_uniform_aux` instantiated with the q-uniform
Backlund bound and the bounded H-Γ(χ) facts: log(q(T+2)) ≤ (log q + log 2 + 1)·log T for T ≥ 3). -/
theorem mainChi (hq : 1 < q) (hprim : χ.IsPrimitive) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      |(NcountL χ T (2 * T) : ℝ) - T / (2 * Real.pi) * ell1q q T| ≤ C * Real.log T := by
  obtain ⟨A, T₀, hA, h⟩ := mainChi_uniform_aux backlund_horizontalChi_uniform GammaChi.gammaFactsChi_uniform
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast (lt_trans Nat.zero_lt_one hq)
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq.le)
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  refine ⟨A * (Real.log q + Real.log 2 + 1), max T₀ 3, fun T hT => ?_⟩
  have hT3 : (3:ℝ) ≤ T := (le_max_right _ _).trans hT
  have hT0 : (0:ℝ) < T := by linarith
  have hlogT : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith
  have hsplit : Real.log (q * (T + 2)) ≤ Real.log q + Real.log 2 + Real.log T := by
    rw [Real.log_mul hq0.ne' (by linarith)]
    have : Real.log (T + 2) ≤ Real.log (2 * T) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul two_ne_zero hT0.ne'] at this
    linarith
  calc |(NcountL χ T (2 * T) : ℝ) - T / (2 * Real.pi) * ell1q q T|
      ≤ A * Real.log (q * (T + 2)) := h q χ hq hprim T ((le_max_left _ _).trans hT)
    _ ≤ A * (Real.log q + Real.log 2 + Real.log T) := mul_le_mul_of_nonneg_left hsplit hA.le
    _ ≤ A * ((Real.log q + Real.log 2 + 1) * Real.log T) := by
        apply mul_le_mul_of_nonneg_left _ hA.le; nlinarith
    _ = A * (Real.log q + Real.log 2 + 1) * Real.log T := by ring

end ThmE
end Zeta23
