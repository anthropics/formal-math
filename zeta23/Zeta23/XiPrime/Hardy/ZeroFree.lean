/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.XiPrime.ExplicitFormula.ZeroFree
import Zeta23.XiPrime.Hardy.Basic

open scoped BigOperators ComplexConjugate
open Complex Set Filter Topology

noncomputable section

namespace Zeta23
namespace XiPrime
namespace Hardy
namespace ZeroFree

open Zeta23.XiPrime.ZeroFree

/-! ## §1. Algebra: L₋, and ζ′/ζ + L₂ = ξ′/ξ − L₋ -/

/-- L₋(s) := ½(L(s) − L(1−s))  (L = Seam.Lfn = Γℝ′/Γℝ + 1/s + 1/(s−1)). -/
def Lm (s : ℂ) : ℂ := (Lfn s - Lfn (1 - s)) / 2

theorem Lm_one_sub (s : ℂ) : Lm (1 - s) = -Lm s := by
  unfold Lm; rw [sub_sub_cancel]; ring

/-- Γℝ′/Γℝ(s) = −½log π + ½ψ(s/2) at every non-real s (Zeta23.RvM.logDeriv_Gammaℝ off the half-plane). -/
theorem logDeriv_Gammaℝ_offreal {s : ℂ} (hs : s.im ≠ 0) :
    logDeriv Complex.Gammaℝ s = -(Real.log Real.pi : ℂ) / 2 + (1 / 2 : ℂ) * Complex.digamma (s / 2) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e : Complex.Gammaℝ = fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) := by
    funext s; rw [Complex.Gammaℝ_def]
  have hf : (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) s ≠ 0 := by
    simp only [ne_eq, cpow_eq_zero_iff, hπ, false_and, not_false_eq_true]
  have hg : (fun s : ℂ => Complex.Gamma (s / 2)) s ≠ 0 :=
    Complex.Gamma_ne_zero (Hardy.half_ne_neg_nat hs)
  have hdf : DifferentiableAt ℂ (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) s :=
    DifferentiableAt.const_cpow (by fun_prop) (Or.inl hπ)
  have hΓ : DifferentiableAt ℂ Complex.Gamma (s / 2) :=
    Complex.differentiableAt_Gamma _ (Hardy.half_ne_neg_nat hs)
  have hdg : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (s / 2)) s := hΓ.comp s (by fun_prop)
  rw [e, logDeriv_mul (f := fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2))
    (g := fun s : ℂ => Complex.Gamma (s / 2)) s hf hg hdf hdg]
  have h1 : logDeriv (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) s = -(Real.log Real.pi : ℂ) / 2 := by
    have hder : HasDerivAt (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2))
        ((Real.pi : ℂ) ^ (-s / 2) * Complex.log Real.pi * (-1 / 2)) s := by
      have : HasDerivAt (fun s : ℂ => -s / 2) (-1 / 2 : ℂ) s := by
        simpa using ((hasDerivAt_id s).neg.div_const (2 : ℂ))
      exact this.const_cpow (Or.inl hπ)
    rw [logDeriv_apply, hder.deriv]
    have hne : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := hf
    rw [Complex.ofReal_log Real.pi_pos.le]
    field_simp
  have h2 : logDeriv (fun s : ℂ => Complex.Gamma (s / 2)) s = (1 / 2 : ℂ) * Complex.digamma (s / 2) := by
    have := logDeriv_comp (f := Complex.Gamma) (g := fun s : ℂ => s / 2) (x := s) hΓ (by fun_prop)
    rw [show (Complex.Gamma ∘ fun s : ℂ => s / 2) = fun s => Complex.Gamma (s / 2) from rfl] at this
    rw [this, Complex.digamma_def]
    have : deriv (fun s : ℂ => s / 2) s = 1 / 2 := by
      rw [deriv_div_const, deriv_id'']
    rw [this]; ring
  rw [h1, h2]

/-- L₋(s) = 1/s + 1/(s−1) + ¼[ψ(s/2) − ψ((1−s)/2)] off the real axis. -/
theorem Lm_eq {s : ℂ} (hs : s.im ≠ 0) :
    Lm s = 1 / s + 1 / (s - 1) + (1 / 4 : ℂ) * (Complex.digamma (s / 2) - Complex.digamma ((1 - s) / 2)) := by
  have h0 : s ≠ 0 := Hardy.ne_zero_of_im_ne_zero hs
  have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr (Hardy.ne_one_of_im_ne_zero hs)
  have h2 : 1 - s ≠ 0 := sub_ne_zero.mpr (Hardy.ne_one_of_im_ne_zero hs).symm
  unfold Lm Lfn
  rw [logDeriv_Gammaℝ_offreal hs, logDeriv_Gammaℝ_offreal (Hardy.im_one_sub_ne_zero hs),
    show (1 : ℂ) - s - 1 = -s by ring]
  field_simp
  ring

/-- L₂(s) = −½log π + ¼[ψ(s/2) + ψ((1−s)/2)] off the real axis. -/
theorem L2_eq_digamma {s : ℂ} (hs : s.im ≠ 0) :
    L2 s = -(Real.log Real.pi : ℂ) / 2
      + (1 / 4 : ℂ) * (Complex.digamma (s / 2) + Complex.digamma ((1 - s) / 2)) := by
  rw [Hardy.L2_eq hs, logDeriv_Gammaℝ_offreal hs, logDeriv_Gammaℝ_offreal (Hardy.im_one_sub_ne_zero hs)]
  ring

/-- ζ′/ζ + L₂ = ξ′/ξ − L₋ on Re s > 0, s ∉ ℝ, ζ(s) ≠ 0. -/
theorem logDeriv_zeta_add_L2 {s : ℂ} (hs : s.im ≠ 0) (hre : 0 < s.re) (hζ : riemannZeta s ≠ 0) :
    logDeriv riemannZeta s + L2 s = logDeriv xi s - Lm s := by
  have h0 : s ≠ 0 := Hardy.ne_zero_of_im_ne_zero hs
  have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr (Hardy.ne_one_of_im_ne_zero hs)
  have h2 : 1 - s ≠ 0 := sub_ne_zero.mpr (Hardy.ne_one_of_im_ne_zero hs).symm
  rw [Hardy.L2_eq hs, logDeriv_xi_eq hre (Hardy.ne_one_of_im_ne_zero hs) hζ, Lm]
  unfold Lfn
  rw [show (1 : ℂ) - s - 1 = -s by ring]
  field_simp
  ring

/-- W = ζ·(ζ′/ζ + L₂) wherever ζ ≠ 0. -/
theorem hardyW_eq_mul {s : ℂ} (hζ : riemannZeta s ≠ 0) :
    hardyW s = riemannZeta s * (logDeriv riemannZeta s + L2 s) := by
  unfold hardyW
  rw [logDeriv_apply]
  field_simp

/-! ## §2. Stirling, real parts -/

/-- ‖ψ(z) − log z‖ ≤ 4 for Re z > 0, |Im z| ≥ 1. -/
theorem norm_digamma_sub_log_le {z : ℂ} (hz : 0 < z.re) (hi : 1 ≤ |z.im|) :
    ‖Complex.digamma z - Complex.log z‖ ≤ 4 := by
  have hst := Zeta23.StirlingVert.digamma_stirling (w := z) hz (by linarith)
  have him2 : 3 / z.im ^ 2 ≤ 3 := by
    rw [div_le_iff₀ (by nlinarith [sq_abs z.im])]
    nlinarith [sq_abs z.im]
  have hnorm : 1 ≤ ‖z‖ := le_trans hi (Complex.abs_im_le_norm z)
  have hinv : ‖(1 / 2 : ℂ) / z‖ ≤ 1 / 2 := by
    rw [norm_div, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by norm_num), div_le_iff₀ (by linarith)]
    linarith
  have e : Complex.digamma z - Complex.log z
      = (Complex.digamma z - Complex.log z + (1 / 2 : ℂ) / z) - (1 / 2 : ℂ) / z := by ring
  rw [e]
  exact (norm_sub_le _ _).trans (by linarith)

/-- Re ψ(z) ≥ log|Im z| − 4 for Re z > 0, |Im z| ≥ 1. -/
theorem re_digamma_ge {z : ℂ} (hz : 0 < z.re) (hi : 1 ≤ |z.im|) :
    Real.log |z.im| - 4 ≤ (Complex.digamma z).re := by
  have h := norm_digamma_sub_log_le hz hi
  have hre : |(Complex.digamma z - Complex.log z).re| ≤ 4 :=
    le_trans (Complex.abs_re_le_norm _) h
  have hre' := (abs_le.mp hre).1
  rw [Complex.sub_re, Complex.log_re] at hre'
  have hlog : Real.log |z.im| ≤ Real.log ‖z‖ :=
    Real.log_le_log (by linarith) (Complex.abs_im_le_norm z)
  linarith

/-- iterated functional equation off the real axis: ψ(z + n) = ψ(z) + Σ_{k<n} 1/(z + k). -/
theorem digamma_add_nat_offreal {z : ℂ} (hz : z.im ≠ 0) (n : ℕ) :
    Complex.digamma (z + n) = Complex.digamma z + ∑ k ∈ Finset.range n, 1 / (z + k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hne : ∀ m : ℕ, z + n ≠ -(m : ℂ) := by
      intro m h
      have := congrArg Complex.im h
      simp only [Complex.add_im, Complex.natCast_im, Complex.neg_im, add_zero, neg_zero] at this
      exact hz this
    rw [Nat.cast_succ, ← add_assoc, Complex.digamma_apply_add_one _ hne, ih, Finset.sum_range_succ,
      one_div]
    ring

/-- Re ψ((1−s)/2) ≥ log(|Im s|/2) − 5 for Re s ≥ 1, |Im s| ≥ 2 (iterate down from Re ∈ (1/2, 3/2]). -/
theorem re_digamma_half_one_sub_ge {s : ℂ} (hre : 1 ≤ s.re) (hi : 2 ≤ |s.im|) :
    Real.log (|s.im| / 2) - 5 ≤ (Complex.digamma ((1 - s) / 2)).re := by
  have hs : s.im ≠ 0 := fun h => by rw [h, abs_zero] at hi; linarith
  set z : ℂ := (1 - s) / 2 with hzdef
  have hzre : z.re = (1 - s.re) / 2 := by simp [hzdef]
  have hzim : z.im = -s.im / 2 := by simp [hzdef]
  have hz : z.im ≠ 0 := by rw [hzim]; intro h; apply hs; linarith
  set N : ℕ := ⌊s.re / 2⌋₊ with hNdef
  have hfl : (N : ℝ) ≤ s.re / 2 := Nat.floor_le (by linarith)
  have hfl2 : s.re / 2 < N + 1 := Nat.lt_floor_add_one (s.re / 2)
  have key := digamma_add_nat_offreal hz (N + 1)
  -- the shifted point z + (N+1) has Re ∈ (1/2, 3/2] and |Im| = |Im s|/2 ≥ 1
  have hwre : 0 < (z + ((N + 1 : ℕ) : ℂ)).re := by
    simp only [Complex.add_re, Complex.natCast_re, hzre]; push_cast; linarith
  have hwim : (z + ((N + 1 : ℕ) : ℂ)).im = -s.im / 2 := by
    simp only [Complex.add_im, Complex.natCast_im, hzim, add_zero]
  have hwim1 : 1 ≤ |(z + ((N + 1 : ℕ) : ℂ)).im| := by
    rw [hwim, abs_div, abs_neg, abs_two]; linarith
  have hψw := re_digamma_ge hwre hwim1
  rw [hwim, abs_div, abs_neg, abs_two] at hψw
  -- the correction terms: all but the last have Re ≤ 0; the last has Re ≤ 1/2
  have hterm : ∀ k : ℕ, (1 / (z + (k : ℂ))).re = (z.re + k) / Complex.normSq (z + k) := by
    intro k; rw [one_div, Complex.inv_re]; simp
  have hfirst : ∑ k ∈ Finset.range N, (1 / (z + (k : ℂ))).re ≤ 0 := by
    apply Finset.sum_nonpos
    intro k hk
    rw [Finset.mem_range] at hk
    have hk' : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
    rw [hterm]
    apply div_nonpos_of_nonpos_of_nonneg _ (Complex.normSq_nonneg _)
    rw [hzre]; linarith
  have hlast : (1 / (z + (N : ℂ))).re ≤ 1 / 2 := by
    rw [hterm]
    have hN1 : 1 ≤ Complex.normSq (z + N) := by
      rw [Complex.normSq_apply]
      have h1 : (z + (N : ℂ)).im = -s.im / 2 := by simp [hzim]
      have h2 : 1 ≤ (-s.im / 2) ^ 2 := by
        have : 1 ≤ |s.im| / 2 := by linarith
        have h3 : (|s.im| / 2) ^ 2 = (-s.im / 2) ^ 2 := by rw [div_pow, div_pow, sq_abs]; ring
        nlinarith
      rw [h1]
      nlinarith [sq_nonneg ((z + (N : ℂ)).re)]
    have hre_le : z.re + N ≤ 1 / 2 := by rw [hzre]; linarith
    rw [div_le_iff₀ (by linarith)]
    linarith
  have hsum : ∑ k ∈ Finset.range (N + 1), (1 / (z + (k : ℂ))).re ≤ 1 / 2 := by
    rw [Finset.sum_range_succ]; linarith
  -- assemble
  have e : (Complex.digamma z).re = (Complex.digamma (z + ((N + 1 : ℕ) : ℂ))).re
      - ∑ k ∈ Finset.range (N + 1), (1 / (z + (k : ℂ))).re := by
    rw [key, Complex.add_re, Complex.re_sum]; ring
  rw [e]
  linarith

/-- Re L₂(σ+it) ≥ ½ log|t| − C for σ ≥ 1, |t| ≥ 2. -/
theorem re_L2_ge : ∃ C : ℝ, ∀ s : ℂ, 1 ≤ s.re → 2 ≤ |s.im| →
    Real.log |s.im| / 2 - C ≤ (L2 s).re := by
  refine ⟨Real.log 2 / 2 + Real.log Real.pi / 2 + 9 / 4, fun s hre hi => ?_⟩
  have hs : s.im ≠ 0 := fun h => by rw [h, abs_zero] at hi; linarith
  have hA : Real.log (|s.im| / 2) - 4 ≤ (Complex.digamma (s / 2)).re := by
    have h := re_digamma_ge (z := s / 2) (by simp; linarith)
      (by rw [Complex.div_ofNat_im, abs_div, abs_two]; linarith)
    rwa [Complex.div_ofNat_im, abs_div, abs_two] at h
  have hB := re_digamma_half_one_sub_ge hre hi
  have hlog : Real.log (|s.im| / 2) = Real.log |s.im| - Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num)]
  have e : (L2 s).re = -(Real.log Real.pi) / 2
      + 1 / 4 * ((Complex.digamma (s / 2)).re + (Complex.digamma ((1 - s) / 2)).re) := by
    rw [L2_eq_digamma hs, show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by norm_num, Complex.add_re,
      Complex.re_ofReal_mul, Complex.add_re]
    congr 1
    rw [show (-(Real.log Real.pi : ℂ) / 2) = (((-(Real.log Real.pi) / 2 : ℝ)) : ℂ) by push_cast; ring,
      Complex.ofReal_re]
  rw [e]
  linarith

set_option maxHeartbeats 800000 in
/-- |Re L₋(σ+it)| ≤ C/t² for 1 ≤ σ ≤ 2, |t| ≥ 4. -/
theorem abs_re_Lm_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 ≤ s.re → s.re ≤ 2 → 4 ≤ |s.im| →
    |(Lm s).re| ≤ C / s.im ^ 2 := by
  refine ⟨11, by norm_num, fun s h1 h2 hi => ?_⟩
  have hs : s.im ≠ 0 := fun h => by rw [h, abs_zero] at hi; linarith
  have hs' : (1 - s).im ≠ 0 := Hardy.im_one_sub_ne_zero hs
  set t : ℝ := s.im with ht
  have ht2 : 16 ≤ t ^ 2 := by nlinarith [sq_abs t]
  have ht0 : 0 < t ^ 2 := by linarith
  -- generic: |Re(1/w)| ≤ |Re w| / (Im w)²
  have hinv : ∀ w : ℂ, w.im ^ 2 = t ^ 2 → |(1 / w).re| ≤ |w.re| / t ^ 2 := by
    intro w hw
    rw [one_div, Complex.inv_re, abs_div, abs_of_nonneg (Complex.normSq_nonneg _)]
    have hN : t ^ 2 ≤ Complex.normSq w := by rw [Complex.normSq_apply, ← hw]; nlinarith
    exact div_le_div_of_nonneg_left (abs_nonneg _) ht0 hN
  -- one functional-equation step for ψ((1−s)/2)
  have hFE : Complex.digamma ((1 - s) / 2) = Complex.digamma ((3 - s) / 2) - 2 / (1 - s) := by
    have h := Complex.digamma_apply_add_one ((1 - s) / 2) (Hardy.half_ne_neg_nat hs')
    rw [show (1 - s) / 2 + 1 = ((3 : ℂ) - s) / 2 by ring] at h
    rw [h]
    have : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Hardy.ne_one_of_im_ne_zero hs).symm
    field_simp
    ring
  -- Stirling remainders at z₁ = s/2 and z₂ = (3−s)/2
  set z₁ : ℂ := s / 2 with hz₁
  set z₂ : ℂ := (3 - s) / 2 with hz₂
  have hz₁re : z₁.re = s.re / 2 := by simp [hz₁]
  have hz₁im : z₁.im = t / 2 := by simp [hz₁, ht]
  have hz₂re : z₂.re = (3 - s.re) / 2 := by simp [hz₂]
  have hz₂im : z₂.im = -t / 2 := by simp [hz₂, ht]
  set E₁ : ℂ := Complex.digamma z₁ - Complex.log z₁ + (1 / 2 : ℂ) / z₁ with hE₁
  set E₂ : ℂ := Complex.digamma z₂ - Complex.log z₂ + (1 / 2 : ℂ) / z₂ with hE₂
  have hE₁b : ‖E₁‖ ≤ 12 / t ^ 2 := by
    have h := Zeta23.StirlingVert.digamma_stirling (w := z₁) (by rw [hz₁re]; linarith)
      (by rw [hz₁im, abs_div, abs_two]; linarith)
    rw [hz₁im] at h
    calc ‖E₁‖ ≤ 3 / (t / 2) ^ 2 := h
      _ = 12 / t ^ 2 := by field_simp; ring
  have hE₂b : ‖E₂‖ ≤ 12 / t ^ 2 := by
    have h := Zeta23.StirlingVert.digamma_stirling (w := z₂) (by rw [hz₂re]; linarith)
      (by rw [hz₂im, abs_div, abs_neg, abs_two]; linarith)
    rw [hz₂im] at h
    calc ‖E₂‖ ≤ 3 / (-t / 2) ^ 2 := h
      _ = 12 / t ^ 2 := by field_simp; ring
  -- the real part of log z₁ − log z₂
  have hn₁ : Complex.normSq z₁ = (s.re ^ 2 + t ^ 2) / 4 := by
    rw [Complex.normSq_apply, hz₁re, hz₁im]; ring
  have hn₂ : Complex.normSq z₂ = ((3 - s.re) ^ 2 + t ^ 2) / 4 := by
    rw [Complex.normSq_apply, hz₂re, hz₂im]; ring
  have hn₁pos : t ^ 2 / 4 ≤ Complex.normSq z₁ := by rw [hn₁]; nlinarith
  have hn₂pos : t ^ 2 / 4 ≤ Complex.normSq z₂ := by rw [hn₂]; nlinarith
  have hlogre : |(Complex.log z₁).re - (Complex.log z₂).re| ≤ 3 / (2 * t ^ 2) := by
    have hl : ∀ z : ℂ, Real.log ‖z‖ = Real.log (Complex.normSq z) / 2 := fun z => by
      rw [Complex.normSq_eq_norm_sq, Real.log_pow]; ring
    rw [Complex.log_re, Complex.log_re, hl, hl]
    set a := Complex.normSq z₁
    set b := Complex.normSq z₂
    have ha : 0 < a := by linarith
    have hb : 0 < b := by linarith
    have hab : |a - b| ≤ 3 / 4 := by
      rw [hn₁, hn₂, abs_le]; constructor <;> nlinarith
    have h1 : Real.log a - Real.log b ≤ |a - b| / (t ^ 2 / 4) := by
      rw [← Real.log_div ha.ne' hb.ne']
      calc Real.log (a / b) ≤ a / b - 1 := Real.log_le_sub_one_of_pos (by positivity)
        _ = (a - b) / b := by field_simp
        _ ≤ |a - b| / b := div_le_div_of_nonneg_right (le_abs_self _) hb.le
        _ ≤ |a - b| / (t ^ 2 / 4) := div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hn₂pos
    have h2 : Real.log b - Real.log a ≤ |a - b| / (t ^ 2 / 4) := by
      rw [← Real.log_div hb.ne' ha.ne']
      calc Real.log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos (by positivity)
        _ = (b - a) / a := by field_simp
        _ ≤ |a - b| / a := div_le_div_of_nonneg_right (by rw [abs_sub_comm]; exact le_abs_self _) ha.le
        _ ≤ |a - b| / (t ^ 2 / 4) := div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hn₁pos
    have h3 : |a - b| / (t ^ 2 / 4) ≤ 3 / t ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) ht0]; nlinarith
    have h4 : (3 : ℝ) / (2 * t ^ 2) = (3 / t ^ 2) / 2 := by ring
    rw [abs_le, h4]
    constructor <;> linarith
  -- the four rational terms
  have r1 : |(1 / s).re| ≤ 2 / t ^ 2 := by
    refine (hinv s (by rw [ht])).trans ?_
    rw [abs_of_pos (by linarith)]
    exact div_le_div_of_nonneg_right h2 ht0.le
  have r2 : |(1 / (s - 1)).re| ≤ 1 / t ^ 2 := by
    refine (hinv (s - 1) (by simp [ht])).trans ?_
    apply div_le_div_of_nonneg_right _ ht0.le
    rw [Complex.sub_re, Complex.one_re, abs_of_nonneg (by linarith)]; linarith
  have r3 : |((1 / 2 : ℂ) / z₁).re| ≤ 2 / t ^ 2 := by
    rw [show (1 / 2 : ℂ) / z₁ = 1 / s by rw [hz₁]; field_simp]
    exact r1
  have r4 : |((1 / 2 : ℂ) / z₂).re| ≤ 2 / t ^ 2 := by
    rw [show (1 / 2 : ℂ) / z₂ = 1 / (3 - s) by rw [hz₂]; field_simp]
    refine (hinv (3 - s) (by simp [ht])).trans ?_
    apply div_le_div_of_nonneg_right _ ht0.le
    rw [Complex.sub_re, show (3 : ℂ).re = 3 by norm_num, abs_of_nonneg (by linarith)]; linarith
  have r5 : |(2 / (1 - s)).re| ≤ 2 / t ^ 2 := by
    rw [show (2 : ℂ) / (1 - s) = 2 * (1 / (1 - s)) by ring,
      show ((2 : ℂ) * (1 / (1 - s))).re = 2 * (1 / (1 - s)).re by simp [Complex.mul_re], abs_mul,
      abs_two]
    have := hinv (1 - s) (by simp [ht])
    rw [Complex.sub_re, Complex.one_re] at this
    have h' : |1 - s.re| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    calc 2 * |(1 / (1 - s)).re| ≤ 2 * (|1 - s.re| / t ^ 2) := by linarith
      _ ≤ 2 * (1 / t ^ 2) := by gcongr
      _ = 2 / t ^ 2 := by ring
  have rE₁ : |E₁.re| ≤ 12 / t ^ 2 := (Complex.abs_re_le_norm _).trans hE₁b
  have rE₂ : |E₂.re| ≤ 12 / t ^ 2 := (Complex.abs_re_le_norm _).trans hE₂b
  -- the formula for Re L₋
  have e : (Lm s).re = (1 / s).re + (1 / (s - 1)).re
      + 1 / 4 * (((Complex.log z₁).re - (Complex.log z₂).re)
        - ((1 / 2 : ℂ) / z₁).re + ((1 / 2 : ℂ) / z₂).re + E₁.re - E₂.re + (2 / (1 - s)).re) := by
    have hψ : Complex.digamma (s / 2) - Complex.digamma ((1 - s) / 2)
        = (Complex.log z₁ - Complex.log z₂) - ((1 / 2 : ℂ) / z₁ - (1 / 2 : ℂ) / z₂) + (E₁ - E₂)
          + 2 / (1 - s) := by
      rw [hFE, hE₁, hE₂, hz₁, hz₂]; ring
    rw [Lm_eq hs, hψ, show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by norm_num]
    simp only [Complex.add_re, Complex.sub_re, Complex.re_ofReal_mul]
    ring
  rw [e]
  have habs := abs_le.mp hlogre
  have := abs_le.mp r1; have := abs_le.mp r2; have := abs_le.mp r3; have := abs_le.mp r4
  have := abs_le.mp r5; have := abs_le.mp rE₁; have := abs_le.mp rE₂
  rw [abs_le]
  constructor
  · have : -(11 / t ^ 2) = -(2 / t ^ 2) - 1 / t ^ 2
        - 1 / 4 * (3 / (2 * t ^ 2) + 2 / t ^ 2 + 2 / t ^ 2 + 12 / t ^ 2 + 12 / t ^ 2 + 2 / t ^ 2)
        - 1 / (8 * t ^ 2) := by ring
    have h5 : 0 ≤ 1 / (8 * t ^ 2) := by positivity
    linarith
  · have : (11 / t ^ 2) = (2 / t ^ 2) + 1 / t ^ 2
        + 1 / 4 * (3 / (2 * t ^ 2) + 2 / t ^ 2 + 2 / t ^ 2 + 12 / t ^ 2 + 12 / t ^ 2 + 2 / t ^ 2)
        + 1 / (8 * t ^ 2) := by ring
    have h5 : 0 ≤ 1 / (8 * t ^ 2) := by positivity
    linarith

/-! ## §3. The zero sum: Re ξ′/ξ(σ+it) ≥ N_T/(8t²) -/

theorem finite_absWindow (T : ℝ) : {ρ : ℂ | IsNontrivialZero ρ ∧ |ρ.im| ≤ T}.Finite := by
  refine (zetaSeam.finite_window (-T - 1) T).subset ?_
  rintro ρ ⟨h1, h2⟩
  have := abs_le.mp h2
  exact ⟨h1, by linarith, this.2⟩

/-- N_T := number of nontrivial zeros ρ of ζ with |Im ρ| ≤ T, counted with multiplicity. -/
def NT (T : ℝ) : ℕ := ∑ ρ ∈ (finite_absWindow T).toFinset, zeroMult ρ

/-- reflection symmetry of the multiset:  Σ_{|γ|≤T} m_ρ (1 − β_ρ) = Σ_{|γ|≤T} m_ρ β_ρ,  hence = N_T/2. -/
theorem sum_mult_one_sub_re (T : ℝ) :
    ∑ ρ ∈ (finite_absWindow T).toFinset, (zeroMult ρ : ℝ) * (1 - ρ.re)
      = ∑ ρ ∈ (finite_absWindow T).toFinset, (zeroMult ρ : ℝ) * ρ.re := by
  have hmem : ∀ ρ, ρ ∈ (finite_absWindow T).toFinset ↔ IsNontrivialZero ρ ∧ |ρ.im| ≤ T := fun ρ => by
    rw [Set.Finite.mem_toFinset]; rfl
  have hrr : ∀ ρ : ℂ, reflect (reflect ρ) = ρ := fun ρ => by simp [reflect]
  have hre : ∀ ρ : ℂ, (reflect ρ).re = 1 - ρ.re := fun ρ => by simp [reflect]
  have hmaps : ∀ ρ ∈ (finite_absWindow T).toFinset, reflect ρ ∈ (finite_absWindow T).toFinset := by
    intro ρ hρ
    rw [hmem] at hρ ⊢
    exact ⟨zeta_reflect_zero ρ hρ.1, by rw [reflect_im]; exact hρ.2⟩
  refine Finset.sum_nbij' reflect reflect hmaps hmaps (fun ρ _ => hrr ρ) (fun ρ _ => hrr ρ) ?_
  intro ρ hρ
  rw [zeta_mult_reflect ρ ((hmem ρ).mp hρ).1, hre]

theorem two_mul_sum_mult_one_sub_re (T : ℝ) :
    2 * ∑ ρ ∈ (finite_absWindow T).toFinset, (zeroMult ρ : ℝ) * (1 - ρ.re) = (NT T : ℝ) := by
  rw [two_mul]
  nth_rewrite 2 [sum_mult_one_sub_re]
  rw [← Finset.sum_add_distrib, NT, Nat.cast_sum]
  exact Finset.sum_congr rfl (fun ρ _ => by ring)

/-- Re ξ′/ξ(σ+it) ≥ N_T/(8t²) for 1 ≤ σ ≤ 2 and |t| ≥ max(2, 2T). -/
theorem re_logDeriv_xi_ge {T : ℝ} (_hT : 0 ≤ T) {s : ℂ} (h1 : 1 ≤ s.re) (h2 : s.re ≤ 2)
    (ht : 2 ≤ |s.im|) (hT2 : 2 * T ≤ |s.im|) :
    (NT T : ℝ) / (8 * s.im ^ 2) ≤ (logDeriv xi s).re := by
  classical
  have hxi : xi s ≠ 0 := xi_ne_zero_of_one_le_re h1
  rw [re_logDeriv_xi_eq_tsum hxi]
  have hsum := summable_re_one_div hxi
  have ht0 : 0 < s.im ^ 2 := by nlinarith [sq_abs s.im]
  set F := (finite_absWindow T).toFinset with hF
  have hmemF : ∀ ρ, ρ ∈ F ↔ IsNontrivialZero ρ ∧ |ρ.im| ≤ T := fun ρ => by
    rw [hF, Set.Finite.mem_toFinset]; rfl
  set f : zetaZeroConfig.carrier → ℝ :=
    fun ρ => (zeroMult ρ : ℝ) * ((s.re - (ρ : ℂ).re) / Complex.normSq (s - ρ)) with hfdef
  have hnonneg : ∀ ρ : zetaZeroConfig.carrier, 0 ≤ f ρ := by
    intro ρ
    have hρ : IsNontrivialZero (ρ : ℂ) := ρ.2
    exact mul_nonneg (Nat.cast_nonneg _) (div_nonneg (by linarith [hρ.2.2]) (Complex.normSq_nonneg _))
  set F' : Finset zetaZeroConfig.carrier := F.subtype (· ∈ zetaZeroConfig.carrier) with hF'
  have hle : ∑ x ∈ F', f x ≤ ∑' x, f x := hsum.sum_le_tsum F' (fun x _ => hnonneg x)
  have heq : ∑ x ∈ F', f x = ∑ ρ ∈ F, (zeroMult ρ : ℝ) * ((s.re - ρ.re) / Complex.normSq (s - ρ)) := by
    have h1 := Finset.sum_subtype_eq_sum_filter (s := F) (p := (· ∈ zetaZeroConfig.carrier))
      (fun ρ : ℂ => (zeroMult ρ : ℝ) * ((s.re - ρ.re) / Complex.normSq (s - ρ)))
    have h2 : F.filter (· ∈ zetaZeroConfig.carrier) = F := by
      apply Finset.filter_true_of_mem
      intro ρ hρ
      exact ((hmemF ρ).mp hρ).1
    rw [h2] at h1
    rw [← h1]
  have hterm : ∀ ρ ∈ F, (zeroMult ρ : ℝ) * (1 - ρ.re) / (4 * s.im ^ 2)
      ≤ (zeroMult ρ : ℝ) * ((s.re - ρ.re) / Complex.normSq (s - ρ)) := by
    intro ρ hρ
    obtain ⟨hz, hγ⟩ := (hmemF ρ).mp hρ
    have hβ0 := hz.2.1
    have hβ1 := hz.2.2
    have habs : |s.im - ρ.im| ≤ 3 / 2 * |s.im| := by
      calc |s.im - ρ.im| ≤ |s.im| + |ρ.im| := abs_sub _ _
        _ ≤ 3 / 2 * |s.im| := by linarith
    have hsq : (s.im - ρ.im) ^ 2 ≤ (3 / 2 * |s.im|) ^ 2 := by
      rw [← sq_abs (s.im - ρ.im)]
      exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    have hN : Complex.normSq (s - ρ) ≤ 4 * s.im ^ 2 := by
      rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
      nlinarith [sq_abs s.im]
    have hNpos : 0 < Complex.normSq (s - ρ) :=
      Complex.normSq_pos.mpr (sub_ne_zero.mpr (fun h => by rw [h] at h1; linarith))
    calc (zeroMult ρ : ℝ) * (1 - ρ.re) / (4 * s.im ^ 2)
        ≤ (zeroMult ρ : ℝ) * (s.re - ρ.re) / (4 * s.im ^ 2) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
      _ ≤ (zeroMult ρ : ℝ) * (s.re - ρ.re) / Complex.normSq (s - ρ) :=
          div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) (by linarith)) hNpos hN
      _ = (zeroMult ρ : ℝ) * ((s.re - ρ.re) / Complex.normSq (s - ρ)) := by ring
  have hhalf := two_mul_sum_mult_one_sub_re T
  calc (NT T : ℝ) / (8 * s.im ^ 2)
      = (∑ ρ ∈ F, (zeroMult ρ : ℝ) * (1 - ρ.re)) / (4 * s.im ^ 2) := by
        rw [← hhalf]; field_simp; ring
    _ = ∑ ρ ∈ F, (zeroMult ρ : ℝ) * (1 - ρ.re) / (4 * s.im ^ 2) := by rw [Finset.sum_div]
    _ ≤ ∑ ρ ∈ F, (zeroMult ρ : ℝ) * ((s.re - ρ.re) / Complex.normSq (s - ρ)) := Finset.sum_le_sum hterm
    _ = ∑ x ∈ F', f x := heq.symm
    _ ≤ ∑' x, f x := hle

/-- N_T → ∞ (Riemann–von Mangoldt). -/
theorem exists_NT_ge (K : ℝ) : ∃ T : ℝ, 0 ≤ T ∧ K ≤ (NT T : ℝ) := by
  classical
  have hRvM := Zeta23.RvM.riemannVonMangoldt Zeta23.gammaFacts
  have h1 := Zeta23.Assembly.eventually_N_ge zetaZeroConfig hRvM
  have h2 : ∀ᶠ T : ℝ in atTop, 4 * Real.pi * K ≤ T * l T :=
    Zeta23.Assembly.tendsto_Tl_atTop.eventually_ge_atTop _
  obtain ⟨T₁, hT1, hT2, hT0⟩ := (h1.and (h2.and (eventually_ge_atTop 0))).exists
  refine ⟨2 * T₁, by linarith, ?_⟩
  have hK : K ≤ (zetaZeroConfig.N T₁ (2 * T₁) : ℝ) := by
    refine le_trans ?_ hT1
    rw [le_div_iff₀ (by positivity)]
    linarith
  refine hK.trans ?_
  have hfinW := zetaZeroConfig.finite_window T₁ (2 * T₁)
  have hN : zetaZeroConfig.N T₁ (2 * T₁) ≤ NT (2 * T₁) := by
    unfold ZeroConfig.N NT
    rw [show zetaZeroConfig.window T₁ (2 * T₁)
        = zetaZeroConfig.carrier ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ 2 * T₁} from rfl,
      finsum_mem_eq_finite_toFinset_sum _ hfinW]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro ρ hρ
      rw [Set.Finite.mem_toFinset] at hρ ⊢
      obtain ⟨hc, hw1, hw2⟩ := hρ
      refine ⟨hc, ?_⟩
      show |ρ.im| ≤ 2 * T₁
      rw [abs_of_pos (by linarith)]
      exact hw2
    · intro _ _ _
      exact Nat.zero_le _
  exact_mod_cast hN

/-! ## §4. W ≠ 0 on Re s ≥ 1, |Im s| ≥ t₀ -/

theorem regionA : ∃ tA : ℝ, 0 < tA ∧ ∀ s : ℂ, 1 ≤ s.re → s.re ≤ 2 → tA ≤ |s.im| →
    0 < (logDeriv xi s - Lm s).re := by
  obtain ⟨C, hC0, hC⟩ := abs_re_Lm_le
  obtain ⟨T, hT0, hT⟩ := exists_NT_ge (8 * C + 8)
  refine ⟨max 4 (2 * T), by positivity, fun s h1 h2 ht => ?_⟩
  have ht4 : 4 ≤ |s.im| := le_trans (le_max_left _ _) ht
  have hT2 : 2 * T ≤ |s.im| := le_trans (le_max_right _ _) ht
  have ht0 : 0 < s.im ^ 2 := by nlinarith [sq_abs s.im]
  have hlow := re_logDeriv_xi_ge hT0 h1 h2 (by linarith) hT2
  have hLm := (abs_le.mp (hC s h1 h2 ht4)).2
  rw [Complex.sub_re]
  have : C / s.im ^ 2 < (NT T : ℝ) / (8 * s.im ^ 2) := by
    rw [div_lt_div_iff₀ ht0 (by positivity)]
    nlinarith
  linarith

theorem regionB : ∃ tB : ℝ, 0 < tB ∧ ∀ s : ℂ, 3 / 2 ≤ s.re → tB ≤ |s.im| →
    0 < (logDeriv riemannZeta s + L2 s).re := by
  obtain ⟨C, hC⟩ := re_L2_ge
  obtain ⟨M, hM0, hM⟩ := norm_logDeriv_zeta_le_far
  refine ⟨max 2 (Real.exp (2 * (C + M) + 1)), by positivity, fun s hre ht => ?_⟩
  have ht2 : 2 ≤ |s.im| := le_trans (le_max_left _ _) ht
  have hlog : 2 * (C + M) + 1 ≤ Real.log |s.im| := by
    rw [← Real.log_exp (2 * (C + M) + 1)]
    exact Real.log_le_log (Real.exp_pos _) (le_trans (le_max_right _ _) ht)
  have hL2 := hC s (by linarith) ht2
  have hζ : -M ≤ (logDeriv riemannZeta s).re := by
    have := (abs_le.mp (le_trans (Complex.abs_re_le_norm _) (hM s hre))).1
    linarith
  rw [Complex.add_re]
  linarith

theorem hardyW_ne_zero_of_one_le_re : ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ s : ℂ, 1 ≤ s.re → t₀ ≤ |s.im| →
    hardyW s ≠ 0 := by
  obtain ⟨tA, htA, hA⟩ := regionA
  obtain ⟨tB, htB, hB⟩ := regionB
  refine ⟨max tA tB, by positivity, fun s hre ht => ?_⟩
  have hs : s.im ≠ 0 := fun h => by
    rw [h, abs_zero] at ht; linarith [le_max_left tA tB]
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re hre
  rw [hardyW_eq_mul hζ]
  refine mul_ne_zero hζ (fun h0 => ?_)
  rcases le_or_gt s.re 2 with h2 | h2
  · have hpos := hA s hre h2 (le_trans (le_max_left _ _) ht)
    rw [← logDeriv_zeta_add_L2 hs (by linarith) hζ, h0, Complex.zero_re] at hpos
    exact lt_irrefl _ hpos
  · have hpos := hB s (by linarith) (le_trans (le_max_right _ _) ht)
    rw [h0, Complex.zero_re] at hpos
    exact lt_irrefl _ hpos

end ZeroFree
end Hardy

/-- **(Z6), unconditionally**: there is a height t₀ > 0 above which every zero of W = ζ′ + L₂ζ lies in the
open critical strip 0 < Re s < 1. -/
theorem wZerosInStrip_holds : ∃ t₀ : ℝ, 0 < t₀ ∧ WZerosInStrip t₀ := by
  obtain ⟨t₀, ht₀, h⟩ := Hardy.ZeroFree.hardyW_ne_zero_of_one_le_re
  refine ⟨t₀, ht₀, fun ρ hρ hρt => ?_⟩
  have him : ρ.im ≠ 0 := fun h0 => by rw [h0, abs_zero] at hρt; linarith
  by_contra hc
  rcases not_and_or.mp hc with h1 | h1
  · -- Re ρ ≤ 0: reflect to 1 − ρ
    have h1' : 1 ≤ (1 - ρ).re := by simp; linarith [not_lt.mp h1]
    have ht' : t₀ ≤ |(1 - ρ).im| := by simpa [abs_neg] using hρt
    exact h (1 - ρ) h1' ht' ((Hardy.hardyW_one_sub_eq_zero_iff him).mpr hρ)
  · exact h ρ (not_lt.mp h1) hρt hρ

end XiPrime
end Zeta23
