/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmE/VerticalLineChi.lean.  The twisted prime side for L(s,χ):
(1/2π)∫ H(c+it)·(−L'/L)(c+it) dt = Σ_n Λ(n)χ(n)n^{−1/2} k(log n), by the same tilted-inversion
device as Zeta23/WeilEF/VerticalLine.lean (tilt/tilted_inversion/Hfn_line are k-generic, reused).
-/
import Zeta23.WeilEF.VerticalLine
import Zeta23.ThmE.LandauChi

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Complex MeasureTheory Real Set
open scoped BigOperators ArithmeticFunction LSeries.notation

namespace Zeta23
namespace ThmE

open Zeta23.WeilEF

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- −L'/L = the twisted Dirichlet series on Re s > 1 (glue of Mathlib's
LSeries_twist_vonMangoldt_eq with the LFunction/LSeries identification). -/
theorem neg_logDeriv_LFunction_eq (_hχ1 : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    -logDeriv χ.LFunction s = LSeries (fun n => (χ n : ℂ) * (Λ n : ℂ)) s := by
  have hds : deriv χ.LFunction s = deriv (LSeries (fun n => (χ n : ℂ))) s := by
    refine Filter.EventuallyEq.deriv_eq ?_
    refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨{z | 1 < z.re},
      (isOpen_lt continuous_const continuous_re).mem_nhds hs, fun z hz => ?_⟩
    exact DirichletCharacter.LFunction_eq_LSeries χ hz
  have h2 := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  rw [logDeriv, Pi.div_apply, hds, DirichletCharacter.LFunction_eq_LSeries χ hs]
  have h3 : (fun n : ℕ => (χ n : ℂ) * (Λ n : ℂ)) = (↗χ * ↗Λ : ℕ → ℂ) := by
    funext n
    simp [Pi.mul_apply]
  rw [h3, h2]
  ring

/-- Pointwise on the line: the integrand as a twisted tsum. -/
theorem integrand_eq_tsum_chi (hχ1 : χ ≠ 1) {k : ℝ → ℂ} {c : ℝ} (hc1 : 1 < c) (t : ℝ) :
    Hfn k ((c:ℝ) + t * I) * (-logDeriv χ.LFunction (((c:ℝ):ℂ) + t * I))
      = ∑' n : ℕ, paperFT (tilt k (c - 1/2)) t
          * LSeries.term (fun n => (χ n : ℂ) * (Λ n : ℂ)) (((c:ℝ):ℂ) + t * I) n := by
  have hre : 1 < ((((c:ℝ)):ℂ) + t * I).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    simpa using hc1
  rw [Hfn_line, neg_logDeriv_LFunction_eq hχ1 hre, LSeries, ← tsum_mul_left]

omit [NeZero q] in
/-- Per-n line integral, twisted: the χ(n)-coefficient rides through the tilted inversion. -/
theorem per_n_line_integral_chi {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {c : ℝ} (n : ℕ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
        paperFT (tilt k (c - 1/2)) t
          * LSeries.term (fun n => (χ n : ℂ) * (Λ n : ℂ)) (((c:ℝ):ℂ) + t * I) n
      = (χ n : ℂ) * ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (Real.log n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term]
  · have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hn0 : (0:ℝ) < (n:ℝ) := by linarith
    have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hterm : ∀ t : ℝ, LSeries.term (fun n => (χ n : ℂ) * (Λ n : ℂ)) (((c:ℝ):ℂ) + t * I) n
        = (χ n : ℂ) * ((Λ n : ℝ) : ℂ) * (((n:ℝ) ^ (-c) : ℝ) : ℂ)
          * cexp (-I * t * Real.log n) := by
      intro t
      rw [LSeries.term_of_ne_zero hn.ne', div_eq_mul_inv, ← Complex.cpow_neg]
      have hsplit : (-((((c:ℝ)):ℂ) + t * I)) = (-((c:ℝ):ℂ)) + (-(I * t)) := by ring
      rw [hsplit, Complex.cpow_add _ _ hnC]
      have h1 : (n:ℂ) ^ (-((c:ℝ):ℂ)) = (((n:ℝ) ^ (-c) : ℝ) : ℂ) := by
        rw [show ((n:ℂ)) = (((n:ℝ):ℂ)) by push_cast; rfl,
          show (-((c:ℝ):ℂ)) = ((-c : ℝ) : ℂ) by push_cast; rfl,
          ← Complex.ofReal_cpow hn0.le]
      have h2 : (n:ℂ) ^ (-(I * t)) = cexp (-I * t * Real.log n) := by
        rw [Complex.cpow_def_of_ne_zero hnC]
        congr 1
        rw [show ((n:ℂ)) = (((n:ℝ):ℂ)) by push_cast; rfl, ← Complex.ofReal_log hn0.le]
        ring
      rw [h1, h2]
      ring
    simp_rw [hterm]
    have hre : (fun t : ℝ => paperFT (tilt k (c - 1/2)) t
        * ((χ n : ℂ) * ((Λ n : ℝ) : ℂ) * (((n:ℝ) ^ (-c) : ℝ) : ℂ) * cexp (-I * t * Real.log n)))
        = fun t : ℝ => ((χ n : ℂ) * ((Λ n : ℝ) : ℂ) * (((n:ℝ) ^ (-c) : ℝ) : ℂ))
          * (paperFT (tilt k (c - 1/2)) t * cexp (-I * t * Real.log n)) := by
      funext t
      ring
    rw [hre, Zeta23.EF.cintegral_const_mul]
    rw [show (1 / (2 * (Real.pi : ℂ))) * (((χ n : ℂ) * ((Λ n : ℝ) : ℂ)
          * (((n:ℝ) ^ (-c) : ℝ) : ℂ))
        * ∫ t : ℝ, paperFT (tilt k (c - 1/2)) t * cexp (-I * t * Real.log n))
        = ((χ n : ℂ) * ((Λ n : ℝ) : ℂ) * (((n:ℝ) ^ (-c) : ℝ) : ℂ))
          * ((1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, paperFT (tilt k (c - 1/2)) t
            * cexp (-I * t * Real.log n)) from by ring]
    rw [tilted_inversion hk hkc (c - 1/2) (Real.log n)]
    have hexp : Real.exp ((c - 1/2) * Real.log n) = (n:ℝ) ^ (c - 1/2) := by
      rw [Real.rpow_def_of_pos hn0]
      ring_nf
    have hpow : ((n:ℝ) ^ (-c) : ℝ) * ((n:ℝ) ^ (c - 1/2) : ℝ) = ((n:ℝ) ^ (-(1/2) : ℝ) : ℝ) := by
      rw [← Real.rpow_add hn0]
      congr 1
      ring
    have hsqrt : ((n:ℝ) ^ (-(1/2) : ℝ) : ℝ) = 1 / Real.sqrt n := by
      rw [Real.rpow_neg hn0.le, Real.sqrt_eq_rpow]
      exact (one_div _).symm
    calc (χ n : ℂ) * ((Λ n : ℝ) : ℂ) * (((n:ℝ) ^ (-c) : ℝ) : ℂ)
        * (k (Real.log n) * ((Real.exp ((c - 1/2) * Real.log n) : ℝ) : ℂ))
        = (χ n : ℂ) * (((Λ n * ((n:ℝ) ^ (-c) * (n:ℝ) ^ (c - 1/2)) : ℝ)) : ℂ)
          * k (Real.log n) := by
          rw [hexp]
          push_cast
          ring
      _ = (χ n : ℂ) * ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (Real.log n) := by
          rw [hpow, hsqrt, mul_one_div]

omit [NeZero q] in
/-- Twisted tsum/integral swap (domination: ‖χ(n)‖ ≤ 1 reduces to the ζ-side majorant). -/
theorem line_integral_swap_chi (_hχ1 : χ ≠ 1) {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {c : ℝ} (hc1 : 1 < c) :
    ∫ t : ℝ, (∑' n : ℕ, paperFT (tilt k (c - 1/2)) t
        * LSeries.term (fun n => (χ n : ℂ) * (Λ n : ℂ)) (((c:ℝ):ℂ) + t * I) n)
      = ∑' n : ℕ, ∫ t : ℝ, paperFT (tilt k (c - 1/2)) t
        * LSeries.term (fun n => (χ n : ℂ) * (Λ n : ℂ)) (((c:ℝ):ℂ) + t * I) n := by
  have hkb2 : ContDiff ℝ 2 (tilt k (c - 1/2)) := tilt_contDiff hk _
  have hkbc : HasCompactSupport (tilt k (c - 1/2)) := tilt_hasCompactSupport hkc _
  have hFkb := Zeta23.EF.integrable_fourier_of_contDiff_two hkb2 hkbc
  have hpfi : Integrable (fun t : ℝ => paperFT (tilt k (c - 1/2)) t) :=
    Zeta23.EF.integrable_paperFT_ofReal hFkb
  have hre : ∀ t : ℝ, ((((c:ℝ)):ℂ) + t * I).re = c := by
    intro t
    simp
  have hnormle : ∀ (n : ℕ) (t : ℝ), ‖LSeries.term (fun n => (χ n : ℂ) * (Λ n : ℂ))
      (((c:ℝ):ℂ) + t * I) n‖ ≤ if n = 0 then (0:ℝ) else (Λ n : ℝ) * ((n:ℝ) ^ (-c)) := by
    intro n t
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn, norm_div, norm_mul,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), hre, if_neg hn,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
      have hχb := DirichletCharacter.norm_le_one χ (n : ZMod q)
      have hrp : (0:ℝ) ≤ ((n:ℝ) ^ (c:ℝ))⁻¹ := by positivity
      have hΛ0 : (0:ℝ) ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
      calc ‖(χ (n : ZMod q) : ℂ)‖ * Λ n * ((n:ℝ) ^ (c:ℝ))⁻¹
          ≤ 1 * Λ n * ((n:ℝ) ^ (c:ℝ))⁻¹ := by gcongr
        _ = Λ n * ((n:ℝ) ^ (c:ℝ))⁻¹ := by ring
  have hcont : ∀ n : ℕ, Continuous (fun t : ℝ =>
      LSeries.term (fun n => (χ n : ℂ) * (Λ n : ℂ)) (((c:ℝ):ℂ) + t * I) n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simpa [LSeries.term_zero] using continuous_const
    · simp only [LSeries.term_of_ne_zero hn]
      refine continuous_const.div ?_ (fun t => ?_)
      · refine Continuous.const_cpow (by fun_prop) (Or.inl ?_)
        exact_mod_cast hn
      · exact cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hn))
  have hint : ∀ n : ℕ, Integrable (fun t : ℝ => paperFT (tilt k (c - 1/2)) t
      * LSeries.term (fun n => (χ n : ℂ) * (Λ n : ℂ)) (((c:ℝ):ℂ) + t * I) n) := by
    intro n
    refine hpfi.mul_bdd (c := if n = 0 then (0:ℝ) else (Λ n : ℝ) * ((n:ℝ) ^ (-c)))
      (hcont n).aestronglyMeasurable ?_
    filter_upwards with t
    exact hnormle n t
  have hcn : Summable (fun n : ℕ => if n = 0 then (0:ℝ) else (Λ n : ℝ) * ((n:ℝ) ^ (-c))) := by
    have hs : LSeriesSummable (fun n => (Λ n : ℂ)) (c : ℂ) :=
      ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hc1)
    have hns : Summable (fun n : ℕ => ‖LSeries.term (fun n => (Λ n : ℂ)) (c : ℂ) n‖) :=
      summable_norm_iff.mpr hs
    refine hns.congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn, norm_div,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), Complex.ofReal_re,
        if_neg hn, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
        Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  have hsum : Summable (fun n : ℕ => ∫ t : ℝ, ‖paperFT (tilt k (c - 1/2)) t
      * LSeries.term (fun n => (χ n : ℂ) * (Λ n : ℂ)) (((c:ℝ):ℂ) + t * I) n‖) := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _)
      (fun n => ?_)
      ((hcn.mul_left (∫ t : ℝ, ‖paperFT (tilt k (c - 1/2)) t‖)))
    calc (∫ t : ℝ, ‖paperFT (tilt k (c - 1/2)) t
          * LSeries.term (fun n => (χ n : ℂ) * (Λ n : ℂ)) (((c:ℝ):ℂ) + t * I) n‖)
        ≤ ∫ t : ℝ, ‖paperFT (tilt k (c - 1/2)) t‖
            * (if n = 0 then (0:ℝ) else (Λ n : ℝ) * ((n:ℝ) ^ (-c))) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
            (hpfi.norm.mul_const _) (Filter.Eventually.of_forall fun t => ?_)
          simp only
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hnormle n t) (norm_nonneg _)
      _ = (∫ t : ℝ, ‖paperFT (tilt k (c - 1/2)) t‖)
            * (if n = 0 then (0:ℝ) else (Λ n : ℝ) * ((n:ℝ) ^ (-c))) := by
          rw [integral_mul_const]
  exact (MeasureTheory.hasSum_integral_of_summable_integral_norm hint hsum).tsum_eq.symm

/-- **The twisted prime side**: (1/2π)∫ H(c+it)(−L'/L)(c+it)dt = Σ Λ(n)χ(n)n^{−1/2}k(log n). -/
theorem prime_side_line_chi (hχ1 : χ ≠ 1) {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {c : ℝ} (hc1 : 1 < c) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, Hfn k ((c:ℝ) + t * I)
        * (-logDeriv χ.LFunction (((c:ℝ):ℂ) + t * I))
      = ∑' n : ℕ, (χ n : ℂ) * ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (Real.log n) := by
  have h1 : ∀ t : ℝ, Hfn k ((c:ℝ) + t * I) * (-logDeriv χ.LFunction (((c:ℝ):ℂ) + t * I))
      = ∑' n : ℕ, paperFT (tilt k (c - 1/2)) t
        * LSeries.term (fun n => (χ n : ℂ) * (Λ n : ℂ)) (((c:ℝ):ℂ) + t * I) n :=
    fun t => integrand_eq_tsum_chi hχ1 hc1 t
  calc (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, Hfn k ((c:ℝ) + t * I)
        * (-logDeriv χ.LFunction (((c:ℝ):ℂ) + t * I))
      = (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, ∑' n : ℕ, paperFT (tilt k (c - 1/2)) t
          * LSeries.term (fun n => (χ n : ℂ) * (Λ n : ℂ)) (((c:ℝ):ℂ) + t * I) n := by
        rw [integral_congr_ae (Filter.Eventually.of_forall h1)]
    _ = (1 / (2 * Real.pi) : ℂ) * ∑' n : ℕ, ∫ t : ℝ, paperFT (tilt k (c - 1/2)) t
          * LSeries.term (fun n => (χ n : ℂ) * (Λ n : ℂ)) (((c:ℝ):ℂ) + t * I) n := by
        rw [line_integral_swap_chi hχ1 hk hkc hc1]
    _ = ∑' n : ℕ, (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, paperFT (tilt k (c - 1/2)) t
          * LSeries.term (fun n => (χ n : ℂ) * (Λ n : ℂ)) (((c:ℝ):ℂ) + t * I) n := by
        rw [← tsum_mul_left]
    _ = ∑' n : ℕ, (χ n : ℂ) * ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (Real.log n) :=
        tsum_congr fun n => per_n_line_integral_chi hk hkc n

end ThmE
end Zeta23
