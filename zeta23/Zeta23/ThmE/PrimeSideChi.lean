/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.PrimeSideA.Basic
import Zeta23.PrimeSideA.Ends
import Zeta23.ThmE.Hypotheses

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

namespace Zeta23
namespace ThmE

open Zeta23.PrimeSide

/-! ## Definitions: the χ-analogues of GentryA / trGtA / trGt2A / MtotalA -/


variable (κ q : ℕ) (c : ℕ → ℂ)

/-- `G_{kl}` for L(s,χ), abstract-taper form (mirror of `GentryA` with `ν_{X,χ}`). -/
def GentryChiA (p : Setting) (F : LocalFun) (k l : ℤ) : ℝ :=
  ∫ τ : ℝ, F.phiHat (τ - p.tau k) * F.phiHat (τ - p.tau l) * nuXc κ q c p.X τ

/-- `tr G̃` for L(s,χ) (abstract). -/
def trGtChiA (p : Setting) (F : LocalFun) : ℝ :=
  (p.L)⁻¹ * ∑ k : Fin p.d, GentryChiA κ q c p F k k

/-- `tr G̃²` for L(s,χ) (abstract). -/
def trGt2ChiA (p : Setting) (F : LocalFun) : ℝ :=
  (p.L)⁻¹ ^ 2 * ∑ k : Fin p.d, ∑ l : Fin p.d, GentryChiA κ q c p F k l ^ 2

/-- `𝓜` for L(s,χ): the bilinear form of [eq:Mdef] with `ν_{X,χ}` in both slots. -/
def MtotalChiA (p : Setting) (F : LocalFun) : ℝ :=
  Mform F.Phi p.T (nuXc κ q c p.X) (nuXc κ q c p.X)

/-! ## The six §5-χ obligations (proofs mirror Zeta23/PrimeSideA.lean) -/

variable {cϱ lam : ℝ}

/-! ## The large-T regime for χ: elementary consequences -/

section RegimeChi

/-- From H-Γ(χ)'s Stirling bound: `|μ_χ| ≤ C·l` on `[T, 2T]` for large `T` (C = C(κ,q)). -/
lemma muq_abs_le (hΓq : GammaFactsChi κ q) (hq : 1 ≤ q) :
    ∃ C T₀ : ℝ, 0 < C ∧ ∀ p : Setting, T₀ ≤ p.T →
      ∀ τ ∈ Set.Icc p.T (2 * p.T), |muq κ q τ| ≤ C * Zeta23.l p.T := by
  obtain ⟨Cs, hCs⟩ := hΓq.stirling
  refine ⟨Real.log q + Real.log 2 + 1 + |Cs|, 2 * π * Real.exp 1, ?_, ?_⟩
  · have h1 : (0:ℝ) ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
    have h2 : (0:ℝ) < Real.log 2 := Real.log_pos one_lt_two
    positivity
  intro p hT τ hτ
  have hπ : (0:ℝ) < π := Real.pi_pos
  have he1 : (1:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hT0 : 2 * π ≤ p.T := by nlinarith
  have hl1 : 1 ≤ Zeta23.l p.T := by
    rw [Zeta23.l, ← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hτpos : (0:ℝ) < τ := by nlinarith [hτ.1, Real.pi_gt_three]
  have hτ1 : 1 ≤ |τ| := by
    rw [abs_of_pos hτpos]
    nlinarith [hτ.1, Real.pi_gt_three]
  have hst := hCs τ hτ1
  have hq0 : (0:ℝ) < q := by exact_mod_cast lt_of_lt_of_le zero_lt_one hq
  have hx1 : (1:ℝ) ≤ (q:ℝ) * |τ| / (2 * π) := by
    rw [le_div_iff₀ (by positivity), abs_of_pos hτpos]
    have h2 : 2 * π ≤ τ := le_trans hT0 hτ.1
    have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
    nlinarith
  have hlog0 : 0 ≤ Real.log ((q:ℝ) * |τ| / (2 * π)) := Real.log_nonneg hx1
  have hlogup : Real.log ((q:ℝ) * |τ| / (2 * π)) ≤ Real.log q + Real.log 2 + Zeta23.l p.T := by
    have hτT : |τ| ≤ 2 * p.T := by
      rw [abs_of_pos hτpos]
      exact hτ.2
    calc Real.log ((q:ℝ) * |τ| / (2 * π)) ≤ Real.log ((q:ℝ) * (2 * p.T) / (2 * π)) := by
          apply Real.log_le_log (by positivity)
          gcongr
      _ = Real.log q + Real.log 2 + Zeta23.l p.T := by
          have hTpos : (0:ℝ) < p.T := by nlinarith
          rw [show (q:ℝ) * (2 * p.T) / (2 * π) = (q:ℝ) * (2 * (p.T / (2 * π))) by ring,
            Real.log_mul (ne_of_gt hq0) (by positivity),
            Real.log_mul (by norm_num) (ne_of_gt (by positivity : (0:ℝ) < p.T / (2 * π))), Zeta23.l]
          ring
  have hCsb : Cs / τ ^ 2 ≤ |Cs| := by
    calc Cs / τ ^ 2 ≤ |Cs| / τ ^ 2 := by gcongr; exact le_abs_self _
      _ ≤ |Cs| / 1 := by
          apply div_le_div_of_nonneg_left (abs_nonneg _) one_pos
          nlinarith [sq_abs τ]
      _ = |Cs| := div_one _
  have h2π : (1:ℝ) ≤ 2 * π := by nlinarith [Real.pi_gt_three]
  calc |muq κ q τ|
      = |(muq κ q τ - (1 / (2 * π)) * Real.log ((q:ℝ) * |τ| / (2 * π)))
          + (1 / (2 * π)) * Real.log ((q:ℝ) * |τ| / (2 * π))| := by ring_nf
    _ ≤ |muq κ q τ - (1 / (2 * π)) * Real.log ((q:ℝ) * |τ| / (2 * π))|
          + |(1 / (2 * π)) * Real.log ((q:ℝ) * |τ| / (2 * π))| := abs_add_le _ _
    _ ≤ |Cs| + (Real.log q + Real.log 2 + Zeta23.l p.T) := by
        have e1 : |(1 / (2 * π)) * Real.log ((q:ℝ) * |τ| / (2 * π))|
            ≤ Real.log q + Real.log 2 + Zeta23.l p.T := by
          rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * π)), abs_of_nonneg hlog0]
          calc 1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π))
              ≤ 1 * Real.log ((q:ℝ) * |τ| / (2 * π)) := by
                apply mul_le_mul_of_nonneg_right _ hlog0
                rw [div_le_one (by positivity)]
                exact h2π
            _ = Real.log ((q:ℝ) * |τ| / (2 * π)) := one_mul _
            _ ≤ Real.log q + Real.log 2 + Zeta23.l p.T := hlogup
        linarith [hst.trans hCsb]
    _ ≤ (Real.log q + Real.log 2 + 1 + |Cs|) * Zeta23.l p.T := by
        have hlq : (0:ℝ) ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
        have hl2 : (0:ℝ) < Real.log 2 := Real.log_pos one_lt_two
        nlinarith [abs_nonneg Cs]

/-- `|P_{X,c}(τ)| ≤ √X` for `X` large (mirror of `PX_abs_le`; only `‖c‖ ≤ 1` is used). -/
lemma PXc_abs_le (hcheb : ChebyshevMertens) (hc : CoeffOK q c) :
    ∃ x₀ : ℝ, 1 ≤ x₀ ∧ ∀ X : ℝ, x₀ ≤ X → ∀ τ : ℝ, |PXc c X τ| ≤ Real.sqrt X := by
  obtain ⟨x₀, hx₀⟩ := hcheb.cheb1b
  refine ⟨max x₀ 1, le_max_right _ _, fun X hX τ => ?_⟩
  have hXx : x₀ ≤ X := (le_max_left _ _).trans hX
  have hX1 : (1:ℝ) ≤ X := (le_max_right _ _).trans hX
  have hπ3 : (3:ℝ) < π := Real.pi_gt_three
  unfold PXc
  rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1 / π)]
  have hsum : |(∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
      ((Λ n : ℝ) : ℂ) * c n * (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * τ)).re|
      ≤ ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, Λ n / Real.sqrt n := by
    refine (Complex.abs_re_le_norm _).trans ?_
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    have hn0 : 0 < n := (Finset.mem_Ioc.1 hn).1
    rw [norm_mul, norm_mul]
    have h1 : ‖((Λ n : ℝ) : ℂ)‖ = Λ n := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    have h2 : ‖(n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * τ)‖ = 1 / Real.sqrt n := by
      rw [Complex.norm_natCast_cpow_of_pos hn0]
      have hre : (-(1 / 2 : ℂ) - Complex.I * τ).re = -(1/2 : ℝ) := by simp
      rw [hre, Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow, one_div]
    rw [h1, h2]
    calc Λ n * ‖c n‖ * (1 / Real.sqrt n) ≤ Λ n * 1 * (1 / Real.sqrt n) := by
          gcongr
          exact hc.norm_le n
      _ = Λ n / Real.sqrt n := by ring
  calc 1 / π * |(∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
        ((Λ n : ℝ) : ℂ) * c n * (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * τ)).re|
      ≤ 1 / π * ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, Λ n / Real.sqrt n := by
        apply mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ 1 / π * (3 * Real.sqrt X) := by
        apply mul_le_mul_of_nonneg_left (hx₀ X hXx) (by positivity)
    _ ≤ Real.sqrt X := by
        rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
        nlinarith [Real.sqrt_nonneg X]

end RegimeChi

/-! ## The P-part Fourier identities for χ (Core-typed; phases via the complex Dirichlet kernel) -/

section PPartChi

variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

/-- Core copy of `integral_phiHat_sq_mul_sin` (the original is typed over full `LocalHyps`). -/
lemma integral_phiHat_sq_mul_sin_core (hF : LocalHypsCoreW cϱ p F) (y : ℝ) :
    ∫ r, F.phiHat r ^ 2 * Real.sin (r * y) = 0 := by
  have h := MeasureTheory.integral_neg_eq_self (fun r => F.phiHat r ^ 2 * Real.sin (r * y))
    MeasureTheory.volume
  simp only [hF.phiHat_even, neg_mul, Real.sin_neg, mul_neg, MeasureTheory.integral_neg] at h
  linarith

/-- Core copy of `integral_phiHat_sq_mul_cos_shift`. -/
lemma integral_phiHat_sq_mul_cos_shift_core (hF : LocalHypsCoreW cϱ p F) (t y : ℝ) :
    ∫ r, F.phiHat r ^ 2 * Real.cos ((t + r) * y) = 2 * π * F.Aphi y * Real.cos (t * y) := by
  have h1 : ∀ r, F.phiHat r ^ 2 * Real.cos ((t + r) * y)
      = Real.cos (t * y) * (F.phiHat r ^ 2 * Real.cos (r * y))
        - Real.sin (t * y) * (F.phiHat r ^ 2 * Real.sin (r * y)) := by
    intro r
    rw [add_mul, Real.cos_add]
    ring
  simp_rw [h1]
  rw [MeasureTheory.integral_sub, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, hF.phiHat_sq_fourier, integral_phiHat_sq_mul_sin_core hF]
  · ring
  · exact (hF.phiHat_sq_mul_integrable_of_bdd (by fun_prop)
      (fun x => Real.abs_cos_le_one _)).const_mul _
  · exact (hF.phiHat_sq_mul_integrable_of_bdd (by fun_prop)
      (fun x => Real.abs_sin_le_one _)).const_mul _

/-- `∫ φ̂(r)² Re(z·e^{−i(t+r)y}) dr = 2π A_φ(y)·Re(z e^{−ity})` — the phase-twisted Fourier identity. -/
lemma integral_phiHat_sq_re_twist_core (hF : LocalHypsCoreW cϱ p F) (z : ℂ) (t y : ℝ) :
    ∫ r, F.phiHat r ^ 2 * (z * Complex.exp (-Complex.I * ((t + r) * y))).re
      = 2 * π * F.Aphi y * (z * Complex.exp (-Complex.I * (t * y))).re := by
  have key : ∀ r : ℝ, (z * Complex.exp (-Complex.I * ((t + r) * y))).re
      = (z * Complex.exp (-Complex.I * (t * y))).re * Real.cos (r * y)
        + (z * Complex.exp (-Complex.I * (t * y))).im * Real.sin (r * y) := by
    intro r
    have e1 : Complex.exp (-Complex.I * ((t + r) * y))
        = Complex.exp (-Complex.I * (t * y)) * Complex.exp (-Complex.I * (r * y)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    rw [e1, ← mul_assoc]
    rw [show -Complex.I * ((r:ℝ) * y) = ((-(r * y) : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    rw [Complex.exp_mul_I]
    simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im,
      Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_im, Real.cos_neg, Real.sin_neg]
    ring_nf
    simp [Complex.I_re, Complex.I_im]
  have e2 : ∀ r : ℝ, F.phiHat r ^ 2 * (z * Complex.exp (-Complex.I * ((t + r) * y))).re
      = (z * Complex.exp (-Complex.I * (t * y))).re * (F.phiHat r ^ 2 * Real.cos (r * y))
        + (z * Complex.exp (-Complex.I * (t * y))).im * (F.phiHat r ^ 2 * Real.sin (r * y)) := by
    intro r
    rw [key r]
    ring
  simp_rw [e2]
  have hint1 : MeasureTheory.Integrable (fun r => F.phiHat r ^ 2 * Real.cos (r * y)) :=
    hF.phiHat_sq_mul_integrable_of_bdd (by fun_prop) (fun x => Real.abs_cos_le_one _)
  have hint2 : MeasureTheory.Integrable (fun r => F.phiHat r ^ 2 * Real.sin (r * y)) :=
    hF.phiHat_sq_mul_integrable_of_bdd (by fun_prop) (fun x => Real.abs_sin_le_one _)
  rw [MeasureTheory.integral_add (hint1.const_mul _) (hint2.const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    hF.phiHat_sq_fourier, integral_phiHat_sq_mul_sin_core hF]
  ring

end PPartChi

/-! ## μ_χ increments and positivity (mirrors of the ζ-side lemmas; constants depend on κ, q) -/

section MuqAnalytic

variable {κ q : ℕ}

/-- Crude global bound: |μ_χ(τ)| ≤ M + |τ| (mirror of mu_linear_bound; q enters only M). -/
lemma muq_linear_bound (hΓq : GammaFactsChi κ q) (hq : 1 ≤ q) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ, |muq κ q τ| ≤ M + |τ| := by
  obtain ⟨C, hC⟩ := hΓq.stirling
  obtain ⟨M₁, hM₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hΓq.smooth.continuous.continuousOn (s := Set.Icc (-1 : ℝ) 1))
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hlq : (0:ℝ) ≤ Real.log q := Real.log_nonneg hq1
  refine ⟨max M₁ (1 + Real.log q + |C|), le_max_of_le_right (by positivity), fun τ => ?_⟩
  rcases le_or_gt 1 |τ| with h1 | h1
  · have hst := hC τ h1
    have hq0 : (0:ℝ) < q := lt_of_lt_of_le zero_lt_one hq1
    have hx : 0 < (q:ℝ) * |τ| / (2 * π) := by positivity
    have hπ3 := Real.pi_gt_three
    have hlog : |Real.log ((q:ℝ) * |τ| / (2 * π))| ≤ Real.log q + |τ| + 2 * π := by
      rw [abs_le]
      constructor
      · have h2 := Real.log_le_sub_one_of_pos (inv_pos.2 hx)
        rw [Real.log_inv] at h2
        have h3 : ((q:ℝ) * |τ| / (2 * π))⁻¹ ≤ 2 * π := by
          rw [inv_div, div_le_iff₀ (by positivity : (0:ℝ) < (q:ℝ) * |τ|)]
          nlinarith [mul_le_mul hq1 h1 zero_le_one (le_trans zero_le_one hq1), Real.pi_pos]
        nlinarith
      · have h2 : Real.log ((q:ℝ) * |τ| / (2 * π)) ≤ Real.log ((q:ℝ) * |τ|) := by
          apply Real.log_le_log hx
          rw [div_le_iff₀ (by positivity)]
          nlinarith [mul_nonneg (le_trans zero_le_one hq1) (abs_nonneg τ), Real.pi_gt_three]
        have h3 : Real.log ((q:ℝ) * |τ|) = Real.log q + Real.log |τ| :=
          Real.log_mul (by positivity) (by positivity)
        have h4 : Real.log |τ| ≤ |τ| - 1 := by
          have := Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one h1)
          linarith
        nlinarith
    have hCτ : C / τ ^ 2 ≤ |C| := by
      calc C / τ ^ 2 ≤ |C| / τ ^ 2 := by gcongr; exact le_abs_self _
        _ ≤ |C| / 1 := by
            apply div_le_div_of_nonneg_left (abs_nonneg _) one_pos
            nlinarith [sq_abs τ]
        _ = |C| := div_one _
    have h2 : |1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π))| ≤ Real.log q + 1 + |τ| := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * π))]
      have h2π1 : (1:ℝ) ≤ 2 * π := by nlinarith
      have e1 : 1 / (2 * π) * |Real.log ((q:ℝ) * |τ| / (2 * π))|
          ≤ 1 / (2 * π) * (Real.log q + |τ| + 2 * π) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      have e2 : 1 / (2 * π) * (Real.log q + |τ| + 2 * π)
          = (Real.log q + |τ|) / (2 * π) + 1 := by field_simp
      have e3 : (Real.log q + |τ|) / (2 * π) ≤ Real.log q + |τ| := by
        apply div_le_self (by positivity)
        exact h2π1
      linarith
    calc |muq κ q τ|
        = |(muq κ q τ - 1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π)))
            + 1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π))| := by ring_nf
      _ ≤ |muq κ q τ - 1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π))|
            + |1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π))| := abs_add_le _ _
      _ ≤ |C| + (Real.log q + 1 + |τ|) := add_le_add (hst.trans hCτ) h2
      _ ≤ max M₁ (1 + Real.log q + |C|) + |τ| := by
          linarith [le_max_right M₁ (1 + Real.log q + |C|)]
  · have := hM₁ τ ⟨by linarith [neg_abs_le τ], by linarith [le_abs_self τ]⟩
    simp only [Real.norm_eq_abs] at this
    linarith [le_max_left M₁ (1 + Real.log q + |C|), abs_nonneg τ]

/-- Increment bound (mirror of mu_increment_bound, unified K(|r| + r²)/t shape). -/
lemma muq_increment_bound (hΓq : GammaFactsChi κ q) (hq : 1 ≤ q) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 2 ≤ t → ∀ r : ℝ,
      |muq κ q (t + r) - muq κ q t| ≤ K * (|r| + r ^ 2) / t := by
  obtain ⟨C₁, hC₁⟩ := hΓq.deriv_bound
  obtain ⟨M, hM0, hM⟩ := muq_linear_bound hΓq hq
  refine ⟨max (2 * |C₁|) (18 * M + 18), le_max_of_le_right (by positivity), fun t ht r => ?_⟩
  have ht0 : 0 < t := by linarith
  rw [le_div_iff₀ ht0]
  rcases le_or_gt |r| (t / 2) with hr | hr
  · have hmvt : ‖muq κ q (t + r) - muq κ q t‖ ≤ (2 * |C₁| / t) * ‖(t + r) - t‖ := by
      apply Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.Icc (t / 2) (3 * t / 2))
      · intro x _
        exact hΓq.smooth.contDiffAt.differentiableAt (by simp)
      · intro x hx
        have hx1 : 1 ≤ |x| := by
          rw [abs_of_pos (by linarith [hx.1])]
          linarith [hx.1]
        calc ‖deriv (muq κ q) x‖ = |deriv (muq κ q) x| := Real.norm_eq_abs _
          _ ≤ C₁ / |x| := hC₁ x hx1
          _ ≤ |C₁| / |x| := by gcongr; exact le_abs_self _
          _ ≤ |C₁| / (t / 2) := by
              apply div_le_div_of_nonneg_left (abs_nonneg _) (by linarith)
              rw [abs_of_pos (by linarith [hx.1])]
              exact hx.1
          _ = 2 * |C₁| / t := by field_simp
      · exact convex_Icc _ _
      · constructor <;> linarith
      · constructor <;> linarith [le_abs_self r, neg_abs_le r]
    simp only [add_sub_cancel_left, Real.norm_eq_abs] at hmvt
    calc |muq κ q (t + r) - muq κ q t| * t ≤ (2 * |C₁| / t * |r|) * t := by gcongr
      _ = 2 * |C₁| * |r| := by field_simp
      _ ≤ max (2 * |C₁|) (18 * M + 18) * (|r| + r ^ 2) := by
          nlinarith [le_max_left (2 * |C₁|) (18 * M + 18), abs_nonneg r, sq_nonneg r,
            le_max_right (2 * |C₁|) (18 * M + 18)]
  · have h1 : |muq κ q (t + r) - muq κ q t| ≤ 2 * M + 2 + 7 * |r| := by
      calc |muq κ q (t + r) - muq κ q t| ≤ |muq κ q (t + r)| + |muq κ q t| := abs_sub _ _
        _ ≤ (M + |t + r|) + (M + |t|) := add_le_add (hM _) (hM _)
        _ ≤ (M + (|t| + |r|)) + (M + |t|) := by linarith [abs_add_le t r]
        _ = 2 * M + 2 * |t| + |r| := by ring
        _ ≤ 2 * M + 2 + 7 * |r| := by
            rw [abs_of_pos ht0]
            nlinarith
    calc |muq κ q (t + r) - muq κ q t| * t ≤ (2 * M + 2 + 7 * |r|) * t := by gcongr
      _ ≤ (2 * M + 2 + 7 * |r|) * (2 * |r|) := by
          apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = (4 * M + 4) * |r| + 14 * |r| ^ 2 := by ring
      _ = (4 * M + 4) * |r| + 14 * r ^ 2 := by rw [sq_abs]
      _ ≤ max (2 * |C₁|) (18 * M + 18) * (|r| + r ^ 2) := by
          nlinarith [le_max_right (2 * |C₁|) (18 * M + 18), abs_nonneg r, sq_nonneg r, hM0]

/-- μ_χ ≥ 0 far out (mirror of mu_nonneg_eventually; uses q ≥ 1 ⇒ log(qτ/2π) ≥ log(τ/2π)). -/
lemma muq_nonneg_eventually (hΓq : GammaFactsChi κ q) (hq : 1 ≤ q) :
    ∃ τ₀ : ℝ, 0 ≤ τ₀ ∧ ∀ x, τ₀ ≤ x → 0 ≤ muq κ q x := by
  obtain ⟨C, hC⟩ := hΓq.stirling
  refine ⟨2 * π * Real.exp (2 * π * |C|), by positivity, fun x hx => ?_⟩
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have h1 : (1:ℝ) ≤ Real.exp (2 * π * |C|) := Real.one_le_exp (by positivity)
  have hπ3 := Real.pi_gt_three
  have hx1 : 1 ≤ x := by nlinarith
  have hx0 : 0 < x := by linarith
  have hst := hC x (by rwa [abs_of_pos hx0])
  rw [abs_of_pos hx0] at hst
  have hlog : 2 * π * |C| ≤ Real.log ((q:ℝ) * x / (2 * π)) := by
    have e1 : Real.exp (2 * π * |C|) ≤ (q:ℝ) * x / (2 * π) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    calc 2 * π * |C| = Real.log (Real.exp (2 * π * |C|)) := (Real.log_exp _).symm
      _ ≤ Real.log ((q:ℝ) * x / (2 * π)) := Real.log_le_log (Real.exp_pos _) e1
  have hCx : C / x ^ 2 ≤ |C| := by
    calc C / x ^ 2 ≤ |C| / x ^ 2 := by gcongr; exact le_abs_self _
      _ ≤ |C| / 1 := by
          apply div_le_div_of_nonneg_left (abs_nonneg _) one_pos
          nlinarith
      _ = |C| := div_one _
  have h2 : |C| ≤ 1 / (2 * π) * Real.log ((q:ℝ) * x / (2 * π)) := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
    linarith
  linarith [(abs_le.1 hst).1]

end MuqAnalytic

/-! ## The complex Dirichlet kernel bound (mirror of the cosine-kernel lemmas) -/

section KernelChi

variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

/-- `|sin(θ/2)|·‖Σ_{k<d} e^{ikθ}‖ ≤ 1` (geometric sum; complex mirror of
`abs_sin_mul_abs_sum_cos_le`). -/
lemma abs_sin_mul_norm_geom_le (θ : ℝ) (d : ℕ) :
    |Real.sin (θ / 2)| * ‖∑ k ∈ Finset.range d, Complex.exp (((k : ℝ) * θ : ℝ) * Complex.I)‖
      ≤ 1 := by
  rcases eq_or_ne (Real.sin (θ / 2)) 0 with hs | hs
  · rw [hs, abs_zero, zero_mul]
    norm_num
  set w : ℂ := Complex.exp ((θ : ℝ) * Complex.I) with hw
  have hsum : ∑ k ∈ Finset.range d, Complex.exp (((k : ℝ) * θ : ℝ) * Complex.I)
      = ∑ k ∈ Finset.range d, w ^ k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hw, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hw1 : w ≠ 1 := by
    intro hww
    rw [hw, Complex.exp_eq_one_iff] at hww
    obtain ⟨n, hn⟩ := hww
    have hθ : θ = n * (2 * π) := by
      have h2 := congrArg Complex.im hn
      simpa [Complex.mul_im, Complex.I_re, Complex.I_im] using h2
    apply hs
    rw [hθ, show (n : ℝ) * (2 * π) / 2 = n * π by ring]
    exact Real.sin_int_mul_pi n
  have hnormw : ‖w - 1‖ = 2 * |Real.sin (θ / 2)| := by
    rw [hw, Complex.exp_mul_I]
    have hre : (Complex.cos ↑θ + Complex.sin ↑θ * Complex.I - 1).re = Real.cos θ - 1 := by
      simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.one_re, Complex.cos_ofReal_re, Complex.sin_ofReal_im, Complex.sin_ofReal_re]
    have him : (Complex.cos ↑θ + Complex.sin ↑θ * Complex.I - 1).im = Real.sin θ := by
      simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.one_im, Complex.cos_ofReal_im, Complex.sin_ofReal_re, Complex.sin_ofReal_im]
    rw [show ‖Complex.cos ↑θ + Complex.sin ↑θ * Complex.I - 1‖
        = Real.sqrt ((Real.cos θ - 1) ^ 2 + Real.sin θ ^ 2) by
      rw [← hre, ← him]
      rw [Complex.norm_eq_sqrt_sq_add_sq]]
    have e : (Real.cos θ - 1) ^ 2 + Real.sin θ ^ 2 = (2 * Real.sin (θ / 2)) ^ 2 := by
      have h1 : Real.cos (2 * (θ / 2)) = 2 * Real.cos (θ / 2) ^ 2 - 1 := Real.cos_two_mul (θ / 2)
      have h2 : Real.sin (θ / 2) ^ 2 + Real.cos (θ / 2) ^ 2 = 1 := Real.sin_sq_add_cos_sq (θ / 2)
      have h3 : 2 * (θ / 2) = θ := by ring
      rw [h3] at h1
      have hpyth := Real.sin_sq_add_cos_sq θ
      nlinarith
    rw [e, Real.sqrt_sq_eq_abs, abs_mul, abs_two]
  have hnormw0 : (0:ℝ) < ‖w - 1‖ := by
    rw [hnormw]
    have := abs_pos.2 hs
    positivity
  rw [hsum, geom_sum_eq hw1, norm_div]
  have hwd : ‖w ^ d - 1‖ ≤ 2 := by
    calc ‖w ^ d - 1‖ ≤ ‖w ^ d‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = ‖w‖ ^ d + 1 := by rw [norm_pow, norm_one]
      _ = 1 + 1 := by
          rw [hw, Complex.norm_exp_ofReal_mul_I, one_pow]
      _ = 2 := by norm_num
  rw [hnormw]
  rw [mul_div_assoc']
  rw [div_le_one (by rw [← hnormw]; exact hnormw0)]
  calc |Real.sin (θ / 2)| * ‖w ^ d - 1‖ ≤ |Real.sin (θ / 2)| * 2 :=
        mul_le_mul_of_nonneg_left hwd (abs_nonneg _)
    _ = 2 * |Real.sin (θ / 2)| := by ring

/-- Mirror of Aphi_mul_sum_cos_le for the complex kernel: A_φ(y)·‖Σ_{k<d} e^{−iτ_k y}‖ ≤ L²/(2 log 2). -/
lemma Aphi_mul_norm_tauKernel_le (hF : LocalHypsCoreW cϱ p F) {y : ℝ} (hy : Real.log 2 ≤ y) :
    F.Aphi y * ‖∑ k ∈ Finset.range p.d, Complex.exp ((-(p.tau k * y) : ℝ) * Complex.I)‖
      ≤ p.L ^ 2 / (2 * Real.log 2) := by
  have hL := hF.L_pos
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog2' : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (zero_lt_two' ℝ)
    linarith
  have hA0 := hF.Aphi_nonneg y
  have hRHS : 0 ≤ p.L ^ 2 / (2 * Real.log 2) := by positivity
  have hyabs : |y| = y := abs_of_nonneg (hlog2.le.trans hy)
  rcases le_or_gt p.L y with hyL | hyL
  · have hz : F.Aphi y = 0 := le_antisymm ((hF.Aphi_le y).trans (by simp [hyabs, hyL])) hA0
    simp [hz, hRHS]
  · set m := min y (p.L - y) with hm
    have hy0 : 0 < y := hlog2.trans_le hy
    have hm0 : 0 < m := lt_min hy0 (by linarith)
    -- factor the kernel
    have hfac : ∑ k ∈ Finset.range p.d, Complex.exp ((-(p.tau k * y) : ℝ) * Complex.I)
        = Complex.exp ((-(p.T * y) : ℝ) * Complex.I)
          * ∑ k ∈ Finset.range p.d, Complex.exp (((k : ℝ) * (-(p.h * y)) : ℝ) * Complex.I) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Complex.exp_add]
      congr 1
      simp only [Setting.tau]
      push_cast
      ring
    have hnorm : ‖∑ k ∈ Finset.range p.d, Complex.exp ((-(p.tau k * y) : ℝ) * Complex.I)‖
        = ‖∑ k ∈ Finset.range p.d, Complex.exp (((k : ℝ) * (-(p.h * y)) : ℝ) * Complex.I)‖ := by
      rw [hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    have hdir := abs_sin_mul_norm_geom_le (-(p.h * y)) p.d
    have hsin_eq : |Real.sin (-(p.h * y) / 2)| = Real.sin (π * y / p.L) := by
      have hθ : p.h * y / 2 = π * y / p.L := by
        simp only [Setting.h]
        field_simp
      rw [show -(p.h * y) / 2 = -(p.h * y / 2) by ring, Real.sin_neg, abs_neg, hθ]
      rw [abs_of_nonneg]
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      · positivity
      · rw [div_le_iff₀ hL]
        nlinarith [Real.pi_pos]
    have hsin : 2 * m / p.L ≤ Real.sin (π * y / p.L) := two_min_div_le_sin hL hy0.le hyL.le
    rw [hnorm]
    set S := ‖∑ k ∈ Finset.range p.d, Complex.exp (((k : ℝ) * (-(p.h * y)) : ℝ) * Complex.I)‖
      with hS
    have hS0 : 0 ≤ S := norm_nonneg _
    rw [hsin_eq] at hdir
    have hS1 : 2 * m / p.L * S ≤ 1 :=
      (mul_le_mul_of_nonneg_right hsin hS0).trans hdir
    have hS2 : 2 * m * S ≤ p.L := by
      have h4 := mul_le_mul_of_nonneg_left hS1 hL.le
      rw [mul_one, ← mul_assoc, mul_div_cancel₀ _ hL.ne'] at h4
      linarith
    have hA1 : F.Aphi y ≤ p.L - y := (hF.Aphi_le y).trans (by simp [hyabs, hyL.le])
    have key : (p.L - y) * Real.log 2 ≤ p.L * m := by
      rcases le_total y (p.L - y) with h | h
      · rw [hm, min_eq_left h]
        nlinarith
      · rw [hm, min_eq_right h]
        nlinarith
    rw [le_div_iff₀ (by positivity)]
    calc F.Aphi y * S * (2 * Real.log 2) ≤ (p.L - y) * S * (2 * Real.log 2) := by gcongr
      _ = ((p.L - y) * Real.log 2) * (2 * S) := by ring
      _ ≤ (p.L * m) * (2 * S) := by gcongr
      _ = p.L * (2 * m * S) := by ring
      _ ≤ p.L * p.L := by gcongr
      _ = p.L ^ 2 := (sq _).symm

/-- sin-analogue of the shifted Fourier identity. -/
lemma integral_phiHat_sq_mul_sin_shift_core (hF : LocalHypsCoreW cϱ p F) (t y : ℝ) :
    ∫ r, F.phiHat r ^ 2 * Real.sin ((t + r) * y) = 2 * π * F.Aphi y * Real.sin (t * y) := by
  have h1 : ∀ r, F.phiHat r ^ 2 * Real.sin ((t + r) * y)
      = Real.sin (t * y) * (F.phiHat r ^ 2 * Real.cos (r * y))
        + Real.cos (t * y) * (F.phiHat r ^ 2 * Real.sin (r * y)) := by
    intro r
    rw [add_mul, Real.sin_add]
    ring
  simp_rw [h1]
  rw [MeasureTheory.integral_add, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, hF.phiHat_sq_fourier, integral_phiHat_sq_mul_sin_core hF]
  · ring
  · exact (hF.phiHat_sq_mul_integrable_of_bdd (by fun_prop)
      (fun x => Real.abs_cos_le_one _)).const_mul _
  · exact (hF.phiHat_sq_mul_integrable_of_bdd (by fun_prop)
      (fun x => Real.abs_sin_le_one _)).const_mul _

/-- **P-part of [prop:trace] for χ at one grid point** (cos/sin-split form):
    ∫ φ̂(r)² P_{X,c}(t+r) dr = −2 Σ_{n≤X} a_n A_φ(log n)·((c n).re cos(t log n) + (c n).im sin(t log n)). -/
lemma P_part_chi_eq (hF : LocalHypsCoreW cϱ p F) (c : ℕ → ℂ) (t : ℝ) :
    ∫ r, F.phiHat r ^ 2 * PXc c p.X (t + r)
      = -2 * ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * F.Aphi (Real.log n)
          * ((c n).re * Real.cos (t * Real.log n) + (c n).im * Real.sin (t * Real.log n)) := by
  have h1 : (fun r => F.phiHat r ^ 2 * PXc c p.X (t + r))
      = fun r => ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊,
          (-(1 / Real.pi) * ((Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ))))
            * ((c n).re * (F.phiHat r ^ 2 * Real.cos ((t + r) * Real.log n))
              + (c n).im * (F.phiHat r ^ 2 * Real.sin ((t + r) * Real.log n))) := by
    funext r
    rw [PXc_eq_sum_cos_sin, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show (t + r) * Real.log n = (t + r) * Real.log n from rfl]
    ring
  rw [h1, MeasureTheory.integral_finsetSum]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add, 
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      integral_phiHat_sq_mul_cos_shift_core hF, integral_phiHat_sq_mul_sin_shift_core hF]
    · have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp
    · exact (hF.phiHat_sq_mul_integrable_of_bdd (by fun_prop)
        (fun x => Real.abs_cos_le_one _)).const_mul _
    · exact (hF.phiHat_sq_mul_integrable_of_bdd (by fun_prop)
        (fun x => Real.abs_sin_le_one _)).const_mul _
  · intro n _
    exact (((hF.phiHat_sq_mul_integrable_of_bdd (by fun_prop)
        (fun x => Real.abs_cos_le_one _)).const_mul _).add
      ((hF.phiHat_sq_mul_integrable_of_bdd (by fun_prop)
        (fun x => Real.abs_sin_le_one _)).const_mul _)).const_mul _

end KernelChi

/-- `P_{X,c}` is continuous in τ. -/
lemma PXc_continuous (_hX : 0 < X) : Continuous (PXc c X) := by
  unfold PXc
  apply Continuous.mul continuous_const
  apply Complex.continuous_re.comp
  apply continuous_finsetSum
  intro n hn
  have hn0 : 0 < n := (Finset.mem_Ioc.1 hn).1
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn0.ne'
  apply Continuous.mul continuous_const
  apply Continuous.const_cpow ?_ (Or.inl hnC)
  fun_prop

/-! ## Diagonal decomposition and the trace bounds for χ -/

section TraceChi

variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {κ q : ℕ} {c : ℕ → ℂ}

/-- μ_χ-part bound at one grid point (mirror of mu_part_bound, K(|r|+r²)/t shape). -/
lemma muq_part_bound (hΓq : GammaFactsChi κ q) (hq : 1 ≤ q) (hF : LocalHypsCoreW cϱ p F) {K : ℝ}
    (_hK0 : 0 ≤ K)
    (hK : ∀ t : ℝ, 2 ≤ t → ∀ r : ℝ, |muq κ q (t + r) - muq κ q t| ≤ K * (|r| + r ^ 2) / t)
    {t : ℝ} (ht : 2 ≤ t) :
    |(∫ r, F.phiHat r ^ 2 * muq κ q (t + r)) - 2 * π * F.a * p.L * muq κ q t|
      ≤ K * ((∫ r, F.phiHat r ^ 2 * |r|) + (∫ r, F.phiHat r ^ 2 * r ^ 2)) / t := by
  have ht0 : (0:ℝ) < t := by linarith
  obtain ⟨M, hM0, hM⟩ := muq_linear_bound hΓq hq
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun r => F.phiHat r ^ 2 * muq κ q (t + r))
      MeasureTheory.volume := by
    have hc' : Continuous fun r => F.phiHat r ^ 2 * muq κ q (t + r) := by
      have h1 := hΓq.smooth.continuous
      have h2 := hF.phiHat_cont
      fun_prop
    exact hc'.aestronglyMeasurable
  have hint : MeasureTheory.Integrable (fun r => F.phiHat r ^ 2 * muq κ q (t + r)) := by
    refine MeasureTheory.Integrable.mono'
      ((hF.phiHat_sq_integrable.const_mul (M + t)).add hF.phiHat_sq_mul_abs_integrable) hmeas ?_
    refine Filter.Eventually.of_forall fun r => ?_
    simp only [Real.norm_eq_abs, Pi.add_apply]
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    have htr : |t + r| ≤ t + |r| := by
      calc |t + r| ≤ |t| + |r| := abs_add_le _ _
        _ = t + |r| := by rw [abs_of_pos ht0]
    calc F.phiHat r ^ 2 * |muq κ q (t + r)| ≤ F.phiHat r ^ 2 * (M + |t + r|) := by
          gcongr
          exact hM _
      _ ≤ F.phiHat r ^ 2 * (M + (t + |r|)) := by gcongr
      _ = (M + t) * F.phiHat r ^ 2 + F.phiHat r ^ 2 * |r| := by ring
  have hconst : 2 * π * F.a * p.L * muq κ q t = ∫ r, F.phiHat r ^ 2 * muq κ q t := by
    rw [MeasureTheory.integral_mul_const, hF.phiHat_sq_integral]
  rw [hconst, ← MeasureTheory.integral_sub hint (hF.phiHat_sq_integrable.mul_const _)]
  have hgi : MeasureTheory.Integrable
      (fun r => K * (F.phiHat r ^ 2 * |r|) / t + K * (F.phiHat r ^ 2 * r ^ 2) / t) :=
    ((hF.phiHat_sq_mul_abs_integrable.const_mul K).div_const t).add
      ((hF.phiHat_sq_mul_sq_integrable.const_mul K).div_const t)
  rw [← Real.norm_eq_abs]
  calc ‖∫ r, F.phiHat r ^ 2 * muq κ q (t + r) - F.phiHat r ^ 2 * muq κ q t‖
      ≤ ∫ r, K * (F.phiHat r ^ 2 * |r|) / t + K * (F.phiHat r ^ 2 * r ^ 2) / t := by
        refine MeasureTheory.norm_integral_le_of_norm_le hgi
          (Filter.Eventually.of_forall fun r => ?_)
        rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg _)]
        calc F.phiHat r ^ 2 * |muq κ q (t + r) - muq κ q t|
            ≤ F.phiHat r ^ 2 * (K * (|r| + r ^ 2) / t) := by
              gcongr
              exact hK t ht r
          _ = K * (F.phiHat r ^ 2 * |r|) / t + K * (F.phiHat r ^ 2 * r ^ 2) / t := by ring
    _ = K * ((∫ r, F.phiHat r ^ 2 * |r|) + (∫ r, F.phiHat r ^ 2 * r ^ 2)) / t := by
        rw [MeasureTheory.integral_add ((hF.phiHat_sq_mul_abs_integrable.const_mul K).div_const t)
          ((hF.phiHat_sq_mul_sq_integrable.const_mul K).div_const t),
          MeasureTheory.integral_div, MeasureTheory.integral_div,
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
        ring

/-- Integrability of φ̂(r)² μ_χ(t+r). -/
lemma muq_part_integrable (hΓq : GammaFactsChi κ q) (hq : 1 ≤ q) (hF : LocalHypsCoreW cϱ p F)
    {t : ℝ} (ht0 : 0 < t) :
    MeasureTheory.Integrable (fun r => F.phiHat r ^ 2 * muq κ q (t + r)) := by
  obtain ⟨M, hM0, hM⟩ := muq_linear_bound hΓq hq
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun r => F.phiHat r ^ 2 * muq κ q (t + r))
      MeasureTheory.volume := by
    have hc' : Continuous fun r => F.phiHat r ^ 2 * muq κ q (t + r) := by
      have h1 := hΓq.smooth.continuous
      have h2 := hF.phiHat_cont
      fun_prop
    exact hc'.aestronglyMeasurable
  refine MeasureTheory.Integrable.mono'
    ((hF.phiHat_sq_integrable.const_mul (M + t)).add hF.phiHat_sq_mul_abs_integrable) hmeas ?_
  refine Filter.Eventually.of_forall fun r => ?_
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  have htr : |t + r| ≤ t + |r| := by
    calc |t + r| ≤ |t| + |r| := abs_add_le _ _
      _ = t + |r| := by rw [abs_of_pos ht0]
  calc F.phiHat r ^ 2 * |muq κ q (t + r)| ≤ F.phiHat r ^ 2 * (M + |t + r|) := by
        gcongr
        exact hM _
    _ ≤ F.phiHat r ^ 2 * (M + (t + |r|)) := by gcongr
    _ = (M + t) * F.phiHat r ^ 2 + F.phiHat r ^ 2 * |r| := by ring

/-- Integrability of φ̂(r)² P_{X,c}(t+r) (bounded × integrable). -/
lemma PXc_part_integrable (hF : LocalHypsCoreW cϱ p F) (hc : CoeffOK q c) (t : ℝ) :
    MeasureTheory.Integrable (fun r => F.phiHat r ^ 2 * PXc c p.X (t + r)) := by
  refine hF.phiHat_sq_mul_integrable_of_bdd
    ((PXc_continuous c p.X_pos).comp (continuous_const_add t))
    (c := 1 / Real.pi * ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊,
      (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * 2) (fun x => ?_)
  rw [PXc_eq_sum_cos_sin, abs_mul, abs_neg,
    abs_of_pos (by positivity : (0:ℝ) < 1 / Real.pi)]
  gcongr
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hn0 : 0 < n := (Finset.mem_Ioc.1 hn).1
  have ha : (0:ℝ) ≤ (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) := by
    have h0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    positivity
  rw [abs_mul, abs_of_nonneg ha]
  gcongr
  have h1 := hc.norm_le n
  have h2 : |(c n).re| ≤ 1 := (Complex.abs_re_le_norm _).trans h1
  have h3 : |(c n).im| ≤ 1 := (Complex.abs_im_le_norm _).trans h1
  calc |(c n).re * Real.cos ((t + x) * Real.log n) + (c n).im * Real.sin ((t + x) * Real.log n)|
      ≤ |(c n).re * Real.cos ((t + x) * Real.log n)|
          + |(c n).im * Real.sin ((t + x) * Real.log n)| := abs_add_le _ _
    _ ≤ 1 * 1 + 1 * 1 := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul h2 (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one)
          (mul_le_mul h3 (Real.abs_sin_le_one _) (abs_nonneg _) zero_le_one)
    _ = 2 := by norm_num

/-- Diagonal decomposition for χ: G_kk = μ_χ-part + P-part (no Π). -/
lemma GentryChiA_diag_eq (hΓq : GammaFactsChi κ q) (hq : 1 ≤ q) (hF : LocalHypsCoreW cϱ p F)
    (hc : CoeffOK q c) (k : ℤ) (hk : 0 < p.tau k) :
    GentryChiA κ q c p F k k = (∫ r, F.phiHat r ^ 2 * muq κ q (p.tau k + r))
      + ∫ r, F.phiHat r ^ 2 * PXc c p.X (p.tau k + r) := by
  unfold GentryChiA
  have htrans : (∫ τ, F.phiHat (τ - p.tau k) * F.phiHat (τ - p.tau k) * nuXc κ q c p.X τ)
      = ∫ r, F.phiHat r ^ 2 * nuXc κ q c p.X (p.tau k + r) := by
    rw [← MeasureTheory.integral_add_right_eq_self _ (p.tau k)]
    congr 1
    funext r
    simp only [add_sub_cancel_right]
    ring_nf
  rw [htrans]
  have hν : ∀ r, F.phiHat r ^ 2 * nuXc κ q c p.X (p.tau k + r)
      = F.phiHat r ^ 2 * muq κ q (p.tau k + r) + F.phiHat r ^ 2 * PXc c p.X (p.tau k + r) := by
    intro r
    simp only [nuXc]
    ring
  simp_rw [hν]
  rw [MeasureTheory.integral_add (muq_part_integrable hΓq hq hF hk) (PXc_part_integrable hF hc _)]

/-- Sum of the P-parts over the grid (mirror of sum_P_part_bound via the complex kernel). -/
lemma sum_P_part_chi_bound (hF : LocalHypsCoreW cϱ p F) (hc : CoeffOK q c) :
    |∑ k ∈ Finset.range p.d, ∫ r, F.phiHat r ^ 2 * PXc c p.X (p.tau k + r)|
      ≤ p.L ^ 2 / Real.log 2 * ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊,
          (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  simp_rw [P_part_chi_eq hF c]
  rw [← Finset.mul_sum, Finset.sum_comm, abs_mul, abs_neg, abs_two]
  have hterm : ∀ n ∈ Finset.Ioc 0 ⌊p.X⌋₊,
      |∑ k ∈ Finset.range p.d, (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * F.Aphi (Real.log n)
          * ((c n).re * Real.cos (p.tau k * Real.log n)
            + (c n).im * Real.sin (p.tau k * Real.log n))|
        ≤ (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * (p.L ^ 2 / (2 * Real.log 2)) := by
    intro n hn
    have hn0 : 0 < n := (Finset.mem_Ioc.1 hn).1
    have ha : (0:ℝ) ≤ (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) := by
      have h0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
      positivity
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · have hn1 : n = 1 := by omega
      subst hn1
      simp [ArithmeticFunction.vonMangoldt_apply_one]
    · have hre : ∀ θ : ℝ, (c n).re * Real.cos θ + (c n).im * Real.sin θ
          = (c n * Complex.exp ((-θ : ℝ) * Complex.I)).re := by
        intro θ
        rw [show ((-θ : ℝ) : ℂ) = -(θ : ℂ) by push_cast; ring]
        rw [show (-(θ:ℂ)) * Complex.I = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring]
        rw [Complex.exp_mul_I]
        simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.mul_im,
          Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im,
          Complex.sin_ofReal_im, Real.cos_neg, Real.sin_neg, Complex.I_re, Complex.I_im]
        ring
      have hsum_eq : ∑ k ∈ Finset.range p.d, (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ))
            * F.Aphi (Real.log n) * ((c n).re * Real.cos (p.tau k * Real.log n)
              + (c n).im * Real.sin (p.tau k * Real.log n))
          = (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * (F.Aphi (Real.log n)
              * (c n * ∑ k ∈ Finset.range p.d,
                  Complex.exp ((-(p.tau k * Real.log n) : ℝ) * Complex.I)).re) := by
        rw [Finset.mul_sum, Complex.re_sum]
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hre (p.tau k * Real.log n)]
        ring
      rw [hsum_eq, abs_mul, abs_of_nonneg ha]
      gcongr
      have hy : Real.log 2 ≤ Real.log n := Real.log_le_log two_pos (by exact_mod_cast hn2)
      have hA0 := hF.Aphi_nonneg (Real.log n)
      calc |F.Aphi (Real.log n) * (c n * ∑ k ∈ Finset.range p.d,
              Complex.exp ((-(p.tau k * Real.log n) : ℝ) * Complex.I)).re|
          = F.Aphi (Real.log n) * |(c n * ∑ k ∈ Finset.range p.d,
              Complex.exp ((-(p.tau k * Real.log n) : ℝ) * Complex.I)).re| := by
            rw [abs_mul, abs_of_nonneg hA0]
        _ ≤ F.Aphi (Real.log n) * ‖∑ k ∈ Finset.range p.d,
              Complex.exp ((-(p.tau k * Real.log n) : ℝ) * Complex.I)‖ := by
            gcongr
            refine (Complex.abs_re_le_norm _).trans ?_
            rw [norm_mul]
            calc ‖c n‖ * ‖∑ k ∈ Finset.range p.d,
                  Complex.exp ((-(p.tau k * Real.log n) : ℝ) * Complex.I)‖
                ≤ 1 * ‖∑ k ∈ Finset.range p.d,
                    Complex.exp ((-(p.tau k * Real.log n) : ℝ) * Complex.I)‖ := by
                  gcongr
                  exact hc.norm_le n
              _ = _ := one_mul _
        _ ≤ p.L ^ 2 / (2 * Real.log 2) := Aphi_mul_norm_tauKernel_le hF hy
  calc 2 * |∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, ∑ k ∈ Finset.range p.d,
          (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * F.Aphi (Real.log n)
          * ((c n).re * Real.cos (p.tau k * Real.log n)
            + (c n).im * Real.sin (p.tau k * Real.log n))|
      ≤ 2 * ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, |∑ k ∈ Finset.range p.d,
          (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * F.Aphi (Real.log n)
          * ((c n).re * Real.cos (p.tau k * Real.log n)
            + (c n).im * Real.sin (p.tau k * Real.log n))| := by
        gcongr
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ 2 * ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊,
          (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) * (p.L ^ 2 / (2 * Real.log 2)) := by
        gcongr with n hn
        exact hterm n hn
    _ = p.L ^ 2 / Real.log 2 * ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊,
          (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ)) := by
        rw [← Finset.sum_mul]
        field_simp

end TraceChi

set_option linter.unusedVariables false in
set_option maxHeartbeats 4000000 in
/-- **[prop:trace] for L(s,χ)** ([thm:E] (iii); no Π-part, μ → μ_{κ,q}, ℓ₁ → ℓ_{1,χ}):
`tr G̃ = aL·N + O_q(L√X)` for any `N` with `|N − Tℓ_{1,χ}/2π| ≤ A log T` (the H-RvM(χ) main shape).
Constants depend on (cϱ, λ, A, κ, q, the H-Γ(χ)/H-cheb constants). -/
theorem prop_trace_chi (hΓq : GammaFactsChi κ q) (hcheb : ChebyshevMertens)
    (hc : CoeffOK q c) (hlam : 0 < lam ∧ lam ≤ 1) (A : ℝ) (hq : 1 ≤ q) :
    ∃ C : ℝ, EventuallyAtCore cϱ lam (fun p F => ∀ N : ℝ,
      |N - p.T / (2 * Real.pi) * ell1q q p.T| ≤ A * Real.log p.T →
      |trGtChiA κ q c p F - F.a * p.L * N| ≤ C * (p.L * Real.sqrt p.X)) := by
  obtain ⟨K, hK0, hK⟩ := muq_increment_bound hΓq hq
  obtain ⟨x₀, hx₀⟩ := hcheb.cheb1b
  obtain ⟨Cml, T₁, hCml0, hCml⟩ := muq_abs_le κ q hΓq hq
  obtain ⟨τ₀, hτ₀0, hτ₀⟩ := muq_nonneg_eventually hΓq hq
  obtain ⟨Cμ, T₂, hCμ⟩ := hΓq.int_mu
  refine ⟨K * (16 + 2 * cϱ + 2 * cϱ ^ 2) + 4 * π * Cml / lam + 5 + |Cμ| + 8 * |A| / lam,
    max (max T₁ 4) (max (2 * π * Real.exp (|x₀| / lam)) (max (τ₀ + 1) (max T₂ 1))),
    fun p F hplam hT hF => ?_⟩
  intro N hN
  have hTa : max T₁ 4 ≤ p.T := (le_max_left _ _).trans hT
  have hTb : max (2 * π * Real.exp (|x₀| / lam)) (max (τ₀ + 1) (max T₂ 1)) ≤ p.T :=
    (le_max_right _ _).trans hT
  have hT₁' : T₁ ≤ p.T := (le_max_left _ _).trans hTa
  have hT4 : 4 ≤ p.T := (le_max_right _ _).trans hTa
  have hTx : 2 * π * Real.exp (|x₀| / lam) ≤ p.T := (le_max_left _ _).trans hTb
  have hTτ : τ₀ + 1 ≤ p.T := ((le_max_left _ _).trans (le_max_right _ _)).trans hTb
  have hT2 : T₂ ≤ p.T := (((le_max_left _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans hTb
  have hT0 : (0:ℝ) < p.T := by linarith
  have hL := hF.L_pos
  have hL8 := hF.eight_le_L
  have hc4 := hF.four_le_cϱ
  have hc0 : (0:ℝ) ≤ cϱ := by linarith
  have hlam0 : 0 < p.lam := hplam ▸ hlam.1
  have hX : x₀ ≤ p.X := Setting.le_X_of_T hlam0 (by rw [hplam]; exact hTx)
  have hX1 : 1 ≤ Real.sqrt p.X := by
    rw [Real.le_sqrt' one_pos, one_pow]
    exact Real.one_le_exp hL.le |>.trans_eq rfl
  have hsX : 0 ≤ Real.sqrt p.X := Real.sqrt_nonneg _
  have hh0 : 0 < p.h := by
    simp only [Setting.h]
    positivity
  have hl1 : (1:ℝ) ≤ Zeta23.l p.T := hF.one_le_l
  have ha1 := hF.a_le_one
  have ha0 := hF.a_pos.le
  set I₁ := ∫ r, F.phiHat r ^ 2 * |r| with hI₁def
  set I₂ := ∫ r, F.phiHat r ^ 2 * r ^ 2 with hI₂def
  have hI₁0 : 0 ≤ I₁ := MeasureTheory.integral_nonneg fun r => by positivity
  have hI₂0 : 0 ≤ I₂ := MeasureTheory.integral_nonneg fun r => by positivity
  have hI₁ : I₁ ≤ 8 + 2 * cϱ * p.L := by
    refine hF.integral_phiHat_sq_mul_abs_le.trans ?_
    have h1 : Real.log (cϱ * p.L / (4 * p.w)) ≤ cϱ * p.L / (4 * p.w) :=
      Real.log_le_self (by have := hF.one_le_w; positivity)
    have h2 : cϱ * p.L / (4 * p.w) ≤ cϱ * p.L / 4 := by
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
      linarith [hF.one_le_w]
    linarith
  have hI₂ : I₂ ≤ 8 + 2 * cϱ ^ 2 := by
    refine hF.integral_phiHat_sq_mul_sq_le.trans ?_
    have h3 : (cϱ / p.w) ^ 2 ≤ cϱ ^ 2 := by
      rw [div_pow]
      exact div_le_self (sq_nonneg _) (by nlinarith [hF.one_le_w])
    linarith
  have hsumFin : ∑ k : Fin p.d, GentryChiA κ q c p F k k
      = ∑ k ∈ Finset.range p.d, GentryChiA κ q c p F k k :=
    Fin.sum_univ_eq_sum_range (fun k => GentryChiA κ q c p F k k) p.d
  have hτg : ∀ k ∈ Finset.range p.d, p.T ≤ p.tau k ∧ p.tau k ≤ 2 * p.T := fun k hk =>
    p.tau_mem hL hT0.le hk
  set Gμ : ℕ → ℝ := fun k => ∫ r, F.phiHat r ^ 2 * muq κ q (p.tau k + r) with hGμ
  set GP : ℕ → ℝ := fun k => ∫ r, F.phiHat r ^ 2 * PXc c p.X (p.tau k + r) with hGP
  have hdecomp : ∑ k ∈ Finset.range p.d, GentryChiA κ q c p F k k
      = ∑ k ∈ Finset.range p.d, Gμ k + ∑ k ∈ Finset.range p.d, GP k := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    exact GentryChiA_diag_eq hΓq hq hF.toCoreW hc k (by linarith [(hτg k hk).1])
  have h1 : |∑ k ∈ Finset.range p.d, Gμ k - 2 * π * F.a * p.L * ∑ k ∈ Finset.range p.d,
      muq κ q (p.tau k)| ≤ p.d * (K * (I₁ + I₂) / p.T) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hbd : ∀ k ∈ Finset.range p.d, |Gμ k - 2 * π * F.a * p.L * muq κ q (p.tau k)|
        ≤ K * (I₁ + I₂) / p.T := by
      intro k hk
      have ht2 : 2 ≤ p.tau k := by linarith [(hτg k hk).1]
      refine (muq_part_bound hΓq hq hF.toCoreW hK0 hK ht2).trans ?_
      exact div_le_div_of_nonneg_left (by positivity) hT0 (hτg k hk).1
    refine (Finset.sum_le_sum hbd).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hhT : p.h ≤ p.T := by
    simp only [Setting.h]
    rw [div_le_iff₀ hL]
    nlinarith [Real.pi_lt_four]
  have hh1 : p.h ≤ 1 := by
    simp only [Setting.h]
    rw [div_le_one hL]
    nlinarith [Real.pi_lt_four]
  have h2 : |2 * π * F.a * p.L * ∑ k ∈ Finset.range p.d, muq κ q (p.tau k)
      - F.a * p.L ^ 2 * ∫ τ in p.T..(2 * p.T), muq κ q τ|
      ≤ 4 * π * Cml * p.L * Zeta23.l p.T := by
    have hR := riemann_sum_monotone (μ := muq κ q) (T := p.T) hh0 hhT
      (hΓq.monotoneOn.mono (fun x hx => by
        simp only [Set.mem_Ici] at hx ⊢
        linarith))
      (fun x hx => hτ₀ x (by linarith))
    rw [← p.d_eq_floor hL] at hR
    have hsum2 : ∑ k ∈ Finset.range p.d, muq κ q (p.tau k)
        = ∑ k ∈ Finset.range p.d, muq κ q (p.T + k * p.h) := by
      refine Finset.sum_congr rfl fun k _ => by rw [Setting.tau_natCast]
    rw [hsum2]
    have hid : 2 * π * F.a * p.L * ∑ k ∈ Finset.range p.d, muq κ q (p.T + k * p.h)
        - F.a * p.L ^ 2 * ∫ τ in p.T..(2 * p.T), muq κ q τ
        = F.a * p.L ^ 2 * (p.h * ∑ k ∈ Finset.range p.d, muq κ q (p.T + k * p.h)
            - ∫ τ in p.T..(2 * p.T), muq κ q τ) := by
      simp only [Setting.h]
      field_simp
    rw [hid, abs_mul, abs_of_nonneg (by positivity)]
    have hμ2T : muq κ q (2 * p.T) ≤ Cml * Zeta23.l p.T := by
      have hv := hCml p hT₁' (2 * p.T) ⟨by linarith, le_rfl⟩
      exact (le_abs_self _).trans hv
    have hμ2T0 : 0 ≤ muq κ q (2 * p.T) := hτ₀ _ (by linarith)
    calc F.a * p.L ^ 2 * |p.h * ∑ k ∈ Finset.range p.d, muq κ q (p.T + k * p.h)
          - ∫ τ in p.T..(2 * p.T), muq κ q τ|
        ≤ F.a * p.L ^ 2 * (2 * p.h * muq κ q (2 * p.T)) := by gcongr
      _ ≤ 1 * p.L ^ 2 * (2 * p.h * (Cml * Zeta23.l p.T)) := by gcongr
      _ = 4 * π * Cml * p.L * Zeta23.l p.T := by
          simp only [Setting.h]
          field_simp
          ring
  have h4 : |∑ k ∈ Finset.range p.d, GP k| ≤ p.L ^ 2 / Real.log 2 * (3 * Real.sqrt p.X) := by
    refine (sum_P_part_chi_bound hF.toCoreW hc).trans ?_
    have hconv : ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ))
        = ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, Λ n / Real.sqrt n := by
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn0 : 0 < n := (Finset.mem_Ioc.1 hn).1
      rw [Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow, div_eq_mul_inv]
    rw [hconv]
    have hnn : (0:ℝ) ≤ p.L ^ 2 / Real.log 2 := by
      have hlog2'' : (0:ℝ) < Real.log 2 := Real.log_pos one_lt_two
      positivity
    exact mul_le_mul_of_nonneg_left (hx₀ p.X hX) hnn
  have hcomb : |∑ k ∈ Finset.range p.d, GentryChiA κ q c p F k k
      - F.a * p.L ^ 2 * ∫ τ in p.T..(2 * p.T), muq κ q τ|
      ≤ p.d * (K * (I₁ + I₂) / p.T) + 4 * π * Cml * p.L * Zeta23.l p.T
        + p.L ^ 2 / Real.log 2 * (3 * Real.sqrt p.X) := by
    rw [hdecomp]
    calc |∑ k ∈ Finset.range p.d, Gμ k + ∑ k ∈ Finset.range p.d, GP k
          - F.a * p.L ^ 2 * ∫ τ in p.T..(2 * p.T), muq κ q τ|
        = |(∑ k ∈ Finset.range p.d, Gμ k
            - 2 * π * F.a * p.L * ∑ k ∈ Finset.range p.d, muq κ q (p.tau k))
          + (2 * π * F.a * p.L * ∑ k ∈ Finset.range p.d, muq κ q (p.tau k)
            - F.a * p.L ^ 2 * ∫ τ in p.T..(2 * p.T), muq κ q τ)
          + ∑ k ∈ Finset.range p.d, GP k| := by ring_nf
      _ ≤ |∑ k ∈ Finset.range p.d, Gμ k
            - 2 * π * F.a * p.L * ∑ k ∈ Finset.range p.d, muq κ q (p.tau k)|
          + |2 * π * F.a * p.L * ∑ k ∈ Finset.range p.d, muq κ q (p.tau k)
            - F.a * p.L ^ 2 * ∫ τ in p.T..(2 * p.T), muq κ q τ|
          + |∑ k ∈ Finset.range p.d, GP k| := abs_add_three _ _ _
      _ ≤ _ := by linarith
  set S := p.L * Real.sqrt p.X with hS
  have hS8 : 8 ≤ S := by nlinarith
  have hS1 : 1 ≤ S := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hLS : p.L ≤ S := by nlinarith
  have hlX : Zeta23.l p.T ≤ 2 / lam * Real.sqrt p.X := by
    have he : Real.sqrt p.X = Real.exp (p.lam * Zeta23.l p.T / 2) := by
      rw [show p.X = Real.exp (p.L) from rfl, ← Real.exp_half]
      rfl
    rw [he, div_mul_eq_mul_div, le_div_iff₀ hlam.1]
    have h1 := Real.add_one_le_exp (p.lam * Zeta23.l p.T / 2)
    rw [hplam] at *
    nlinarith [hlam.1]
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog2' : (0:ℝ) < Real.log 2 := by linarith
  have hd : (p.d : ℝ) ≤ p.L * p.T / (2 * π) := p.d_le (by positivity)
  have hπ1 : (1:ℝ) ≤ 2 * π := by nlinarith [Real.pi_gt_three]
  have t1 : (p.d : ℝ) * (K * (I₁ + I₂) / p.T)
      ≤ p.L * (K * (16 + 2 * cϱ + 2 * cϱ ^ 2) * S) := by
    have e1 : (p.d : ℝ) * (K * (I₁ + I₂) / p.T)
        ≤ p.L * p.T / (2 * π) * (K * (I₁ + I₂) / p.T) := by
      gcongr
    have e2 : p.L * p.T / (2 * π) * (K * (I₁ + I₂) / p.T)
        = p.L * (K * (I₁ + I₂)) / (2 * π) := by
      field_simp
    have e3 : I₁ + I₂ ≤ (16 + 2 * cϱ + 2 * cϱ ^ 2) * p.L := by
      have u1 : (16:ℝ) ≤ 16 * p.L := by nlinarith
      have u3 : 2 * cϱ ^ 2 ≤ 2 * cϱ ^ 2 * p.L := by nlinarith [sq_nonneg cϱ]
      nlinarith
    calc (p.d : ℝ) * (K * (I₁ + I₂) / p.T) ≤ p.L * (K * (I₁ + I₂)) / (2 * π) := by
          rw [← e2]
          exact e1
      _ ≤ p.L * (K * (I₁ + I₂)) := by
          apply div_le_self (by positivity)
          exact hπ1
      _ ≤ p.L * (K * ((16 + 2 * cϱ + 2 * cϱ ^ 2) * p.L)) := by gcongr
      _ = p.L * (K * (16 + 2 * cϱ + 2 * cϱ ^ 2)) * p.L := by ring
      _ ≤ p.L * (K * (16 + 2 * cϱ + 2 * cϱ ^ 2)) * S := by
          have hnn : (0:ℝ) ≤ p.L * (K * (16 + 2 * cϱ + 2 * cϱ ^ 2)) := by positivity
          exact mul_le_mul_of_nonneg_left hLS hnn
      _ = p.L * (K * (16 + 2 * cϱ + 2 * cϱ ^ 2) * S) := by ring
  have t2 : 4 * π * Cml * p.L * Zeta23.l p.T ≤ p.L * (4 * π * Cml / lam * S) := by
    have e1 : Zeta23.l p.T ≤ S / lam := by
      rw [le_div_iff₀ hlam.1]
      calc Zeta23.l p.T * lam ≤ (2 / lam * Real.sqrt p.X) * lam := by
            gcongr
            exact hlam.1.le
        _ = 2 * Real.sqrt p.X := by
            have hne := hlam.1.ne'
            field_simp
        _ ≤ p.L * Real.sqrt p.X := by
            exact mul_le_mul_of_nonneg_right (by linarith) hsX
        _ = S := hS.symm
    calc 4 * π * Cml * p.L * Zeta23.l p.T ≤ 4 * π * Cml * p.L * (S / lam) := by
          gcongr
      _ = p.L * (4 * π * Cml / lam * S) := by
          have hne := hlam.1.ne'
          field_simp
  have t4 : p.L ^ 2 / Real.log 2 * (3 * Real.sqrt p.X) ≤ p.L * (5 * S) := by
    have e1 : p.L ^ 2 / Real.log 2 * (3 * Real.sqrt p.X) = p.L * ((3 / Real.log 2) * S) := by
      rw [hS]
      field_simp
    rw [e1]
    gcongr
    rw [div_le_iff₀ hlog2']
    nlinarith
  have hmu_form : |trGtChiA κ q c p F - F.a * p.L * ∫ τ in p.T..(2 * p.T), muq κ q τ|
      ≤ (K * (16 + 2 * cϱ + 2 * cϱ ^ 2) + 4 * π * Cml / lam + 5) * S := by
    have htr : trGtChiA κ q c p F - F.a * p.L * ∫ τ in p.T..(2 * p.T), muq κ q τ
        = p.L⁻¹ * (∑ k ∈ Finset.range p.d, GentryChiA κ q c p F k k
            - F.a * p.L ^ 2 * ∫ τ in p.T..(2 * p.T), muq κ q τ) := by
      simp only [trGtChiA, hsumFin]
      field_simp
    rw [htr, abs_mul, abs_of_pos (inv_pos.2 hL)]
    calc p.L⁻¹ * |∑ k ∈ Finset.range p.d, GentryChiA κ q c p F k k
          - F.a * p.L ^ 2 * ∫ τ in p.T..(2 * p.T), muq κ q τ|
        ≤ p.L⁻¹ * (p.L * (K * (16 + 2 * cϱ + 2 * cϱ ^ 2) * S)
            + p.L * (4 * π * Cml / lam * S) + p.L * (5 * S)) := by
          gcongr
          refine hcomb.trans ?_
          linarith
      _ = (K * (16 + 2 * cϱ + 2 * cϱ ^ 2) + 4 * π * Cml / lam + 5) * S := by
          field_simp
  have hT1' : (1:ℝ) ≤ p.T := by linarith
  have hμint := hCμ p.T hT2
  have e2' : |F.a * p.L * ((∫ τ in p.T..(2 * p.T), muq κ q τ) - p.T * ell1q q p.T / (2 * π))|
      ≤ |Cμ| * S := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg ha0 hL.le)]
    have hi : |(∫ τ in p.T..(2 * p.T), muq κ q τ) - p.T * ell1q q p.T / (2 * π)| ≤ |Cμ| := by
      refine hμint.trans ?_
      calc Cμ / p.T ≤ |Cμ| / p.T := by gcongr; exact le_abs_self _
        _ ≤ |Cμ| / 1 := by
            apply div_le_div_of_nonneg_left (abs_nonneg _) one_pos
            exact hT1'
        _ = |Cμ| := div_one _
    calc F.a * p.L * |(∫ τ in p.T..(2 * p.T), muq κ q τ) - p.T * ell1q q p.T / (2 * π)|
        ≤ 1 * p.L * |Cμ| := by gcongr
      _ = p.L * |Cμ| := by ring
      _ ≤ S * |Cμ| := mul_le_mul_of_nonneg_right hLS (abs_nonneg _)
      _ = |Cμ| * S := by ring
  have e3' : |F.a * p.L * (p.T * ell1q q p.T / (2 * π) - N)| ≤ 8 * |A| / lam * S := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg ha0 hL.le), abs_sub_comm]
    have hlogT : Real.log p.T ≤ Zeta23.l p.T + 3 := by
      have e1 : Zeta23.l p.T = Real.log p.T - Real.log (2 * π) := by
        rw [Zeta23.l, Real.log_div (ne_of_gt hT0) (by positivity)]
      have hlog2π : Real.log (2 * π) ≤ 3 := by
        rw [show (3:ℝ) = Real.log (Real.exp 3) by rw [Real.log_exp]]
        apply Real.log_le_log (by nlinarith [Real.pi_gt_three])
        have he1 := Real.exp_one_gt_d9
        have he3 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add, ← Real.exp_add]
          norm_num
        have hp2 : (7.3:ℝ) ≤ Real.exp 1 * Real.exp 1 := by nlinarith
        have hp3 : (19:ℝ) ≤ Real.exp 1 * Real.exp 1 * Real.exp 1 := by nlinarith
        rw [he3]
        nlinarith [Real.pi_lt_four]
      linarith
    have hwin : |N - p.T * ell1q q p.T / (2 * π)| ≤ |A| * (Zeta23.l p.T + 3) := by
      rw [show p.T * ell1q q p.T / (2 * π) = p.T / (2 * π) * ell1q q p.T by ring]
      refine hN.trans ?_
      have hlogT0 : (0:ℝ) ≤ Real.log p.T := Real.log_nonneg hT1'
      calc A * Real.log p.T ≤ |A| * Real.log p.T :=
            mul_le_mul_of_nonneg_right (le_abs_self A) hlogT0
        _ ≤ |A| * (Zeta23.l p.T + 3) := mul_le_mul_of_nonneg_left hlogT (abs_nonneg A)
    calc F.a * p.L * |N - p.T * ell1q q p.T / (2 * π)|
        ≤ 1 * p.L * (|A| * (Zeta23.l p.T + 3)) := by gcongr
      _ = p.L * (|A| * (Zeta23.l p.T + 3)) := by ring
      _ ≤ p.L * (|A| * (4 * Zeta23.l p.T)) := by
          gcongr
          linarith
      _ ≤ p.L * (|A| * (4 * (2 / lam * Real.sqrt p.X))) := by gcongr
      _ = 8 * |A| / lam * (p.L * Real.sqrt p.X) := by
          have hne := hlam.1.ne'
          field_simp
          ring
      _ = 8 * |A| / lam * S := by rw [hS]
  calc |trGtChiA κ q c p F - F.a * p.L * N|
      = |(trGtChiA κ q c p F - F.a * p.L * ∫ τ in p.T..(2 * p.T), muq κ q τ)
          + F.a * p.L * ((∫ τ in p.T..(2 * p.T), muq κ q τ) - p.T * ell1q q p.T / (2 * π))
          + F.a * p.L * (p.T * ell1q q p.T / (2 * π) - N)| := by ring_nf
    _ ≤ |trGtChiA κ q c p F - F.a * p.L * ∫ τ in p.T..(2 * p.T), muq κ q τ|
          + |F.a * p.L * ((∫ τ in p.T..(2 * p.T), muq κ q τ) - p.T * ell1q q p.T / (2 * π))|
          + |F.a * p.L * (p.T * ell1q q p.T / (2 * π) - N)| := abs_add_three _ _ _
    _ ≤ (K * (16 + 2 * cϱ + 2 * cϱ ^ 2) + 4 * π * Cml / lam + 5 + |Cμ| + 8 * |A| / lam) * S := by
        linarith [hmu_form, e2', e3']


set_option linter.unusedVariables false in
/-- **[eq:Msplit] for L(s,χ)**: three terms only (`Π_X ≡ 0`):
`𝓜 = 𝓜[μ_χ,μ_χ] + 𝓜[P,P] + 2𝓜[μ_χ,P]`. -/
theorem eq_Msplit_chi (hΓq : GammaFactsChi κ q) (hc : CoeffOK q c)
    (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ T₀ : ℝ, ∀ (p : Setting) (F : LocalFun), p.lam = lam → T₀ ≤ p.T →
      LocalHypsCore cϱ p F →
      MtotalChiA κ q c p F
        = Mform F.Phi p.T (muq κ q) (muq κ q)
          + Mform F.Phi p.T (PXc c p.X) (PXc c p.X)
          + 2 * Mform F.Phi p.T (muq κ q) (PXc c p.X) := by
  refine ⟨1, fun p F hplam hT hF => ?_⟩
  have hμc : Continuous (muq κ q) := hΓq.smooth.continuous
  have hPc : Continuous (PXc c p.X) := PXc_continuous c p.X_pos
  have hΦ : Continuous F.Phi := hF.Phi_contDiff.continuous
  have hΦe : ∀ r, F.Phi (-r) = F.Phi r := hF.Phi_even
  have hsum : Continuous (muq κ q + PXc c p.X) := hμc.add hPc
  have he : MtotalChiA κ q c p F = Mform F.Phi p.T (muq κ q + PXc c p.X) (muq κ q + PXc c p.X) := by
    unfold MtotalChiA nuXc
    rfl
  rw [he, Mform_add_left hΦ hμc hPc hsum, Mform_add_right hΦ hμc hPc hμc,
    Mform_add_right hΦ hμc hPc hPc, Mform_comm hΦe (PXc c p.X) (muq κ q)]
  ring


set_option maxHeartbeats 1600000 in
/-- μ_χ satisfies the `NuBound` μ-part: `|μ_χ(τ)| ≤ C₀·l + log⁺(|τ|/4T)` for large `T`
(three ranges: |τ| ≤ 1 via the linear bound; 1 ≤ |τ| ≤ 4T and |τ| > 4T via Stirling). -/
lemma muq_nuBound (hΓq : GammaFactsChi κ q) (hq : 1 ≤ q) :
    ∃ C₀ T₀ : ℝ, 1 ≤ C₀ ∧ ∀ p : Setting, T₀ ≤ p.T → ∀ τ : ℝ,
      |muq κ q τ| ≤ C₀ * Zeta23.l p.T + max (Real.log (|τ| / (4 * p.T))) 0 := by
  obtain ⟨M, hM0, hM⟩ := muq_linear_bound hΓq hq
  obtain ⟨Cs, hCs⟩ := hΓq.stirling
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hlq : (0:ℝ) ≤ Real.log q := Real.log_nonneg hq1
  refine ⟨max 1 (M + Real.log q + |Cs| + 10), 2 * π * Real.exp 1, le_max_left _ _,
    fun p hT τ => ?_⟩
  set C₀ := max 1 (M + Real.log q + |Cs| + 10) with hC₀
  have hπ : (0:ℝ) < π := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  have he1 : (1:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
  have hT0 : (0:ℝ) < p.T := by nlinarith
  have hl1 : 1 ≤ Zeta23.l p.T := by
    rw [Zeta23.l, ← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hl0 : (0:ℝ) ≤ Zeta23.l p.T := by linarith
  have hC₀M : M + Real.log q + |Cs| + 10 ≤ C₀ := le_max_right _ _
  have hC₀1 : (1:ℝ) ≤ C₀ := le_max_left _ _
  have hmax0 : (0:ℝ) ≤ max (Real.log (|τ| / (4 * p.T))) 0 := le_max_right _ _
  have hlogT : Real.log p.T ≤ Zeta23.l p.T + 3 := by
    have e1 : Zeta23.l p.T = Real.log p.T - Real.log (2 * π) := by
      rw [Zeta23.l, Real.log_div (ne_of_gt hT0) (by positivity)]
    have hlog2π : (0:ℝ) ≤ Real.log (2 * π) := Real.log_nonneg (by nlinarith)
    have hlog2π' : Real.log (2 * π) ≤ 3 := by
      rw [show (3:ℝ) = Real.log (Real.exp 3) by rw [Real.log_exp]]
      apply Real.log_le_log (by positivity)
      have he3 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add, ← Real.exp_add]
        norm_num
      have hee := Real.exp_one_gt_d9
      have hp2 : (7.3:ℝ) ≤ Real.exp 1 * Real.exp 1 := by nlinarith
      have hp3 : (19:ℝ) ≤ Real.exp 1 * Real.exp 1 * Real.exp 1 := by nlinarith
      rw [he3]
      nlinarith [Real.pi_lt_four]
    linarith
  rcases le_or_gt |τ| 1 with hτ1 | hτ1
  · -- small |τ|
    have h1 : |muq κ q τ| ≤ M + 1 := by
      have := hM τ
      linarith
    have h2 : M + 1 ≤ C₀ * Zeta23.l p.T := by
      calc M + 1 ≤ C₀ * 1 := by
            rw [mul_one]
            linarith [abs_nonneg Cs]
        _ ≤ C₀ * Zeta23.l p.T := by
            apply mul_le_mul_of_nonneg_left hl1
            linarith
    linarith
  · -- |τ| ≥ 1: Stirling
    have hτ0 : (0:ℝ) < |τ| := by linarith
    have hst := hCs τ hτ1.le
    have hCsb : Cs / τ ^ 2 ≤ |Cs| := by
      calc Cs / τ ^ 2 ≤ |Cs| / τ ^ 2 := by gcongr; exact le_abs_self _
        _ ≤ |Cs| / 1 := by
            apply div_le_div_of_nonneg_left (abs_nonneg _) one_pos
            nlinarith [sq_abs τ]
        _ = |Cs| := div_one _
    have hbase : |muq κ q τ| ≤ 1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π)) + |Cs|
        ∨ Real.log ((q:ℝ) * |τ| / (2 * π)) < 0 := by
      rcases le_or_gt 0 (Real.log ((q:ℝ) * |τ| / (2 * π))) with hpos | hneg
      · left
        have h1 := (abs_le.1 hst).2
        have h2 := (abs_le.1 hst).1
        have h3 : |muq κ q τ| ≤ |muq κ q τ - 1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π))|
            + 1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π)) := by
          have := abs_add_le (muq κ q τ - 1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π)))
            (1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π)))
          simp only [sub_add_cancel] at this
          refine this.trans ?_
          have habs : |1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π))|
              = 1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π)) := by
            rw [abs_of_nonneg (by positivity)]
          rw [habs]
        linarith [hst.trans hCsb]
      · right
        exact hneg
    have hfrac1 : 1 / (2 * π) ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    -- in the negative-log case the Stirling bound already gives |μq| ≤ |Cs|
    rcases hbase with hb | hneg
    · -- split the log
      have hlogsplit : Real.log ((q:ℝ) * |τ| / (2 * π))
          = Real.log q + Real.log |τ| - Real.log (2 * π) := by
        rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity)
          (ne_of_gt hτ0)]
      have hlog2π0 : (0:ℝ) ≤ Real.log (2 * π) := Real.log_nonneg (by nlinarith)
      rcases le_or_gt |τ| (4 * p.T) with hτT | hτT
      · -- middle range
        have hlogτ : Real.log |τ| ≤ Real.log 4 + Real.log p.T := by
          rw [← Real.log_mul (by norm_num) (ne_of_gt hT0)]
          exact Real.log_le_log hτ0 hτT
        have hlog4 : Real.log 4 ≤ 2 := by
          rw [show (2:ℝ) = Real.log (Real.exp 2) by rw [Real.log_exp]]
          apply Real.log_le_log (by norm_num)
          have hee := Real.exp_one_gt_d9
          have hp2 : (7.3:ℝ) ≤ Real.exp 1 * Real.exp 1 := by nlinarith
          have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
            rw [← Real.exp_add]
            norm_num
          nlinarith
        have hchain : |muq κ q τ| ≤ Real.log q + (Zeta23.l p.T + 5) + |Cs| := by
          have h4 : Real.log ((q:ℝ) * |τ| / (2 * π)) ≤ Real.log q + (Zeta23.l p.T + 5) := by
            rw [hlogsplit]
            linarith
          have h5 : 1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π))
              ≤ Real.log q + (Zeta23.l p.T + 5) := by
            rcases le_or_gt 0 (Real.log ((q:ℝ) * |τ| / (2 * π))) with hpos | hneg2
            · calc 1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π))
                  ≤ 1 * Real.log ((q:ℝ) * |τ| / (2 * π)) :=
                    mul_le_mul_of_nonneg_right hfrac1 hpos
                _ = Real.log ((q:ℝ) * |τ| / (2 * π)) := one_mul _
                _ ≤ Real.log q + (Zeta23.l p.T + 5) := h4
            · have : 1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π)) ≤ 0 := by
                apply mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg2.le
              nlinarith
          linarith
        have hfin : Real.log q + (Zeta23.l p.T + 5) + |Cs| ≤ C₀ * Zeta23.l p.T := by
          have h9 : M + Real.log q + |Cs| + 10 ≤ C₀ := hC₀M
          have h10 : C₀ * Zeta23.l p.T = C₀ + C₀ * (Zeta23.l p.T - 1) := by ring
          have h11 : Zeta23.l p.T - 1 ≤ C₀ * (Zeta23.l p.T - 1) :=
            le_mul_of_one_le_left (by linarith) hC₀1
          linarith
        linarith
      · -- far range
        have hlogτ : Real.log |τ| = Real.log (|τ| / (4 * p.T)) + Real.log (4 * p.T) := by
          rw [← Real.log_mul (by
            intro h0
            have := div_eq_zero_iff.1 h0
            rcases this with h | h
            · exact (ne_of_gt hτ0) h
            · nlinarith) (by positivity)]
          congr 1
          field_simp
        have hratio1 : (1:ℝ) ≤ |τ| / (4 * p.T) := by
          rw [le_div_iff₀ (by positivity)]
          linarith
        have hlogr0 : 0 ≤ Real.log (|τ| / (4 * p.T)) := Real.log_nonneg hratio1
        have hmaxeq : max (Real.log (|τ| / (4 * p.T))) 0 = Real.log (|τ| / (4 * p.T)) :=
          max_eq_left hlogr0
        have hlog4T : Real.log (4 * p.T) ≤ 2 + (Zeta23.l p.T + 3) := by
          rw [Real.log_mul (by norm_num) (ne_of_gt hT0)]
          have hlog4 : Real.log 4 ≤ 2 := by
            rw [show (2:ℝ) = Real.log (Real.exp 2) by rw [Real.log_exp]]
            apply Real.log_le_log (by norm_num)
            have hee := Real.exp_one_gt_d9
            have hp2 : (7.3:ℝ) ≤ Real.exp 1 * Real.exp 1 := by nlinarith
            have he2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
              rw [← Real.exp_add]
              norm_num
            nlinarith
          linarith
        have h4 : Real.log ((q:ℝ) * |τ| / (2 * π))
            ≤ Real.log q + Real.log (|τ| / (4 * p.T)) + (Zeta23.l p.T + 5) := by
          rw [hlogsplit, hlogτ]
          linarith
        have h5 : 1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π))
            ≤ Real.log q + Real.log (|τ| / (4 * p.T)) + (Zeta23.l p.T + 5) := by
          rcases le_or_gt 0 (Real.log ((q:ℝ) * |τ| / (2 * π))) with hpos | hneg2
          · calc 1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π))
                ≤ 1 * Real.log ((q:ℝ) * |τ| / (2 * π)) :=
                  mul_le_mul_of_nonneg_right hfrac1 hpos
              _ = Real.log ((q:ℝ) * |τ| / (2 * π)) := one_mul _
              _ ≤ _ := h4
          · have h6 : 1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π)) ≤ 0 := by
              apply mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg2.le
            nlinarith
        have hfin : Real.log q + (Zeta23.l p.T + 5) + |Cs| ≤ C₀ * Zeta23.l p.T := by
          have h9 : M + Real.log q + |Cs| + 10 ≤ C₀ := hC₀M
          have h10 : C₀ * Zeta23.l p.T = C₀ + C₀ * (Zeta23.l p.T - 1) := by ring
          have h11 : Zeta23.l p.T - 1 ≤ C₀ * (Zeta23.l p.T - 1) :=
            le_mul_of_one_le_left (by linarith) hC₀1
          linarith
        rw [hmaxeq]
        linarith
    · -- log < 0: |μq| ≤ |Cs| directly
      have h1 : |muq κ q τ| ≤ |Cs| + 1 / (2 * π) * |Real.log ((q:ℝ) * |τ| / (2 * π))| := by
        have h2 := hst.trans hCsb
        have h3 := abs_add_le (muq κ q τ - 1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π)))
          (1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π)))
        simp only [sub_add_cancel] at h3
        have h4 : |1 / (2 * π) * Real.log ((q:ℝ) * |τ| / (2 * π))|
            = 1 / (2 * π) * |Real.log ((q:ℝ) * |τ| / (2 * π))| := by
          rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * π))]
        linarith
      -- |log| when log < 0: the argument ≥ |τ|/(2π·…)… bound |log| ≤ log 2π (argument ≥ q|τ|/2π ≥ 1/(2π))
      have harg : (1:ℝ) / (2 * π) ≤ (q:ℝ) * |τ| / (2 * π) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        nlinarith
      have h5 : |Real.log ((q:ℝ) * |τ| / (2 * π))| ≤ Real.log (2 * π) := by
        rw [abs_of_neg hneg]
        have h6 := Real.log_le_log (by positivity : (0:ℝ) < 1 / (2 * π)) harg
        rw [Real.log_div one_ne_zero (by positivity), Real.log_one] at h6
        linarith
      have hlog2π' : Real.log (2 * π) ≤ 3 := by
        rw [show (3:ℝ) = Real.log (Real.exp 3) by rw [Real.log_exp]]
        apply Real.log_le_log (by positivity)
        have he3 : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
          rw [← Real.exp_add, ← Real.exp_add]
          norm_num
        have hee := Real.exp_one_gt_d9
        have hp2 : (7.3:ℝ) ≤ Real.exp 1 * Real.exp 1 := by nlinarith
        have hp3 : (19:ℝ) ≤ Real.exp 1 * Real.exp 1 * Real.exp 1 := by nlinarith
        rw [he3]
        nlinarith [Real.pi_lt_four]
      have hchain : |muq κ q τ| ≤ |Cs| + 3 := by
        have h7 : 1 / (2 * π) * |Real.log ((q:ℝ) * |τ| / (2 * π))| ≤ 3 := by
          calc 1 / (2 * π) * |Real.log ((q:ℝ) * |τ| / (2 * π))|
              ≤ 1 * |Real.log ((q:ℝ) * |τ| / (2 * π))| :=
                mul_le_mul_of_nonneg_right hfrac1 (abs_nonneg _)
            _ = |Real.log ((q:ℝ) * |τ| / (2 * π))| := one_mul _
            _ ≤ Real.log (2 * π) := h5
            _ ≤ 3 := hlog2π'
        linarith
      have hfin : |Cs| + 3 ≤ C₀ * Zeta23.l p.T := by
        have h8 : |Cs| + 3 ≤ C₀ := by linarith
        have h10 : C₀ * 1 ≤ C₀ * Zeta23.l p.T :=
          mul_le_mul_of_nonneg_left hl1 (by linarith)
        linarith
      linarith

set_option linter.unusedVariables false in
/-- **[lem:ends] for L(s,χ)**: `tr G̃² = 𝓜 + O_q(L·l·log l·(l² + X))` (same error shape as ζ:
`B_χ = ℓ_{1,χ} + 4√X ≤ C_q(l + √X)` and the ψ-tail machinery is coefficient-independent). -/
theorem lem_ends_chi (hΓq : GammaFactsChi κ q) (hcheb : ChebyshevMertens)
    (hc : CoeffOK q c) (hlam : 0 < lam ∧ lam ≤ 1) (hq : 1 ≤ q) :
    ∃ C : ℝ, EventuallyAtCore cϱ lam (fun p F =>
      |trGt2ChiA κ q c p F - MtotalChiA κ q c p F|
        ≤ C * (p.L * Zeta23.l p.T * Real.log (Zeta23.l p.T) * (Zeta23.l p.T ^ 2 + p.X))) := by
  obtain ⟨Cends, T₀e, hends⟩ := Zeta23.PrimeSide.lem_ends_nu (cϱ := cϱ) (lam := lam)
  obtain ⟨C₀, T₀μ, hC₀1, hμB⟩ := muq_nuBound (κ := κ) (q := q) hΓq hq
  obtain ⟨x₀, hx₀1, hPb⟩ := PXc_abs_le (q := q) (c := c) hcheb hc
  refine ⟨|Cends| * (2 * C₀ ^ 2 + 2),
    max T₀e (max T₀μ (2 * π * Real.exp (|x₀| / lam))), fun p F hplam hT hF => ?_⟩
  have hTe : T₀e ≤ p.T := (le_max_left _ _).trans hT
  have hTμ : T₀μ ≤ p.T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
  have hTx : 2 * π * Real.exp (|x₀| / lam) ≤ p.T :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hT
  have hlam0 : 0 < p.lam := hplam ▸ hlam.1
  have hX : x₀ ≤ p.X := Setting.le_X_of_T hlam0 (by rw [hplam]; exact hTx)
  have hL := hF.L_pos
  have hl1 : (1:ℝ) ≤ Zeta23.l p.T := hF.one_le_l
  have hsX : 0 ≤ Real.sqrt p.X := Real.sqrt_nonneg _
  set B : ℝ := C₀ * Zeta23.l p.T + Real.sqrt p.X with hB
  have hcont : Continuous (nuXc κ q c p.X) := by
    have h1 : (nuXc κ q c p.X) = fun τ => muq κ q τ + PXc c p.X τ := rfl
    rw [h1]
    exact (hΓq.smooth.continuous).add (PXc_continuous c p.X_pos)
  have hnu : Zeta23.PrimeSide.NuBound p B (nuXc κ q c p.X) := by
    intro τ
    have h1 : |nuXc κ q c p.X τ| ≤ |muq κ q τ| + |PXc c p.X τ| := by
      have h0 : nuXc κ q c p.X τ = muq κ q τ + PXc c p.X τ := rfl
      rw [h0]
      exact abs_add_le _ _
    have h2 := hμB p hTμ τ
    have h3 := hPb p.X hX τ
    rw [hB]
    linarith
  have hlB : Zeta23.l p.T ≤ B := by
    rw [hB]
    nlinarith
  have hmain := hends p F B (nuXc κ q c p.X) hplam hTe hF hcont hnu hlB
  have heq : trGt2ChiA κ q c p F - MtotalChiA κ q c p F
      = (p.L)⁻¹ ^ 2 * ∑ k : Fin p.d, ∑ l : Fin p.d,
          Zeta23.PrimeSide.GentryNu (nuXc κ q c p.X) p F k l ^ 2
        - Zeta23.PrimeSide.MtotalNu (nuXc κ q c p.X) p F := rfl
  show |trGt2ChiA κ q c p F - MtotalChiA κ q c p F| ≤ _
  rw [heq]
  refine hmain.trans ?_
  have hB2 : B ^ 2 ≤ (2 * C₀ ^ 2 + 2) * (Zeta23.l p.T ^ 2 + p.X) := by
    have hsq : Real.sqrt p.X ^ 2 = p.X := Real.sq_sqrt (le_of_lt p.X_pos)
    have hC₀0 : (0:ℝ) ≤ C₀ := by linarith
    rw [hB]
    nlinarith [sq_nonneg (C₀ * Zeta23.l p.T - Real.sqrt p.X), sq_nonneg (Zeta23.l p.T),
      sq_nonneg (Real.sqrt p.X), mul_nonneg (mul_nonneg hC₀0 hC₀0) (sq_nonneg (Zeta23.l p.T))]
  have hlog0 : 0 ≤ Real.log (Zeta23.l p.T) := Real.log_nonneg hl1
  calc Cends * (p.L * p.l * Real.log p.l * B ^ 2)
      ≤ |Cends| * (p.L * p.l * Real.log p.l * B ^ 2) := by
        apply mul_le_mul_of_nonneg_right (le_abs_self _)
        positivity
    _ ≤ |Cends| * (p.L * p.l * Real.log p.l * ((2 * C₀ ^ 2 + 2) * (Zeta23.l p.T ^ 2 + p.X))) := by
        gcongr
    _ = |Cends| * (2 * C₀ ^ 2 + 2)
        * (p.L * Zeta23.l p.T * Real.log (Zeta23.l p.T) * (Zeta23.l p.T ^ 2 + p.X)) := by
        ring


end ThmE
end Zeta23
