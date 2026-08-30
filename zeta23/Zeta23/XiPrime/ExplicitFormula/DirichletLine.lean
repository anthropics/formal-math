/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
A Dirichlet series with general complex coefficients against the Weil test
weight on a vertical line:
    (1/2π) ∫_ℝ H(c+it) · Σ_N a_N N^{−(c+it)} dt = Σ_N a_N N^{−1/2} k(log N),
H = Zeta23.WeilEF.Hfn k, for k ∈ C_c²(ℝ), any real c, and Σ_N ‖a_N‖ N^{−c} < ∞.
[XF′ Thm 4.2 (e)].
-/
import Zeta23.WeilEF.Main
import Mathlib.Analysis.Normed.Group.FunctionSeries

noncomputable section

namespace Zeta23
namespace XiPrime

open Complex MeasureTheory
open Zeta23.WeilEF (Hfn tilt Hfn_line tilted_inversion tilt_contDiff tilt_hasCompactSupport)

/-- the L-series term on the line, factored: a_N · N^{−c} · e^{−it log N}. -/
theorem LSeries_term_line (a : ℕ → ℂ) (c t : ℝ) {n : ℕ} (hn : n ≠ 0) :
    LSeries.term a ((c : ℂ) + t * I) n
      = a n * ((((n : ℝ) ^ (-c) : ℝ)) : ℂ) * cexp (-I * t * Real.log n) := by
  have hn' : 0 < n := Nat.pos_of_ne_zero hn
  have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn'
  have hnC : (n:ℂ) ≠ 0 := by exact_mod_cast hn
  rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg]
  have hsplit : (-((c:ℂ) + t * I)) = (-(c:ℂ)) + (-(I * t)) := by ring
  rw [hsplit, Complex.cpow_add _ _ hnC]
  have h1 : (n:ℂ) ^ (-(c:ℂ)) = (((n:ℝ) ^ (-c) : ℝ) : ℂ) := by
    rw [show ((n:ℂ)) = (((n:ℝ):ℂ)) by push_cast; rfl,
      show (-(c:ℂ)) = ((-c : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_cpow hn0.le]
  have h2 : (n:ℂ) ^ (-(I * t)) = cexp (-I * t * Real.log n) := by
    rw [Complex.cpow_def_of_ne_zero hnC]
    congr 1
    rw [show ((n:ℂ)) = (((n:ℝ):ℂ)) by push_cast; rfl, ← Complex.ofReal_log hn0.le]
    ring
  rw [h1, h2]
  ring

/-- norm of the L-series term on the line Re s = c. -/
theorem norm_LSeries_term_line (a : ℕ → ℂ) (c t : ℝ) (n : ℕ) :
    ‖LSeries.term a ((c : ℂ) + t * I) n‖ = if n = 0 then (0:ℝ) else ‖a n‖ * ((n:ℝ) ^ (-c)) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_zero]
  · have hre : ((c:ℂ) + t * I).re = c := by simp
    rw [LSeries.term_of_ne_zero hn, norm_div,
      Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), hre, if_neg hn,
      Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

/-- Step 1 (pointwise): H(c+it) · L(a, c+it) = Σ' paperFT(tilt k (c−1/2)) t · term_N. -/
theorem integrand_eq_tsum_gen (k : ℝ → ℂ) (a : ℕ → ℂ) (c t : ℝ) :
    Hfn k (c + t * I) * LSeries a (c + t * I)
      = ∑' n : ℕ, paperFT (tilt k (c - 1/2)) t * LSeries.term a (c + t * I) n := by
  rw [Hfn_line, LSeries, ← tsum_mul_left]

/-- Step 2 (per-N line integral): (1/2π)∫ paperFT(tilt k (c−1/2)) t · term_N(c+it) dt
  = a_N N^{−1/2} k(log N). -/
theorem per_n_line_integral_gen {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (a : ℕ → ℂ) (c : ℝ) (n : ℕ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
        paperFT (tilt k (c - 1/2)) t * LSeries.term a (c + t * I) n
      = a n / ((Real.sqrt n : ℝ) : ℂ) * k (Real.log n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term]
  · have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    simp_rw [LSeries_term_line a c _ hn.ne']
    have hre : (fun t : ℝ => paperFT (tilt k (c - 1/2)) t
        * (a n * (((n:ℝ) ^ (-c) : ℝ) : ℂ) * cexp (-I * t * Real.log n)))
        = fun t : ℝ => (a n * (((n:ℝ) ^ (-c) : ℝ) : ℂ))
          * (paperFT (tilt k (c - 1/2)) t * cexp (-I * t * Real.log n)) := by
      funext t
      ring
    rw [hre, Zeta23.EF.cintegral_const_mul]
    rw [show (1 / (2 * (Real.pi : ℂ))) * ((a n * (((n:ℝ) ^ (-c) : ℝ) : ℂ))
        * ∫ t : ℝ, paperFT (tilt k (c - 1/2)) t * cexp (-I * t * Real.log n))
        = (a n * (((n:ℝ) ^ (-c) : ℝ) : ℂ))
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
    calc a n * (((n:ℝ) ^ (-c) : ℝ) : ℂ)
        * (k (Real.log n) * ((Real.exp ((c - 1/2) * Real.log n) : ℝ) : ℂ))
        = a n * (((n:ℝ) ^ (-c) : ℝ) : ℂ)
          * (k (Real.log n) * (((n:ℝ) ^ (c - 1/2) : ℝ) : ℂ)) := by rw [hexp]
      _ = a n * ((((n:ℝ) ^ (-c) * (n:ℝ) ^ (c - 1/2) : ℝ)) : ℂ) * k (Real.log n) := by
          push_cast
          ring
      _ = a n / ((Real.sqrt n : ℝ) : ℂ) * k (Real.log n) := by
          rw [hpow, hsqrt]
          push_cast
          ring

/-- continuity of each L-series term along the line. -/
theorem continuous_LSeries_term_line (a : ℕ → ℂ) (c : ℝ) (n : ℕ) :
    Continuous (fun t : ℝ => LSeries.term a ((c:ℂ) + t * I) n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simpa [LSeries.term_zero] using continuous_const
  · simp only [LSeries.term_of_ne_zero hn]
    refine continuous_const.div ?_ (fun t => ?_)
    · refine Continuous.const_cpow (by fun_prop) (Or.inl ?_)
      exact_mod_cast hn
    · exact cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hn))

/-- the summable majorant of the term norms. -/
theorem summable_coeff_bound (a : ℕ → ℂ) (c : ℝ)
    (ha : Summable (fun N : ℕ => ‖a N‖ * (N : ℝ) ^ (-c))) :
    Summable (fun n : ℕ => if n = 0 then (0:ℝ) else ‖a n‖ * ((n:ℝ) ^ (-c))) := by
  refine (summable_nat_add_iff 1).mp ?_
  have := (summable_nat_add_iff 1).mpr ha
  refine this.congr fun n => ?_
  simp

/-- continuity of t ↦ L(a, c+it) (uniformly convergent series of continuous functions). -/
theorem continuous_LSeries_line (a : ℕ → ℂ) (c : ℝ)
    (ha : Summable (fun N : ℕ => ‖a N‖ * (N : ℝ) ^ (-c))) :
    Continuous (fun t : ℝ => LSeries a ((c:ℂ) + t * I)) := by
  have h := continuous_tsum (continuous_LSeries_term_line a c) (summable_coeff_bound a c ha)
    (fun n t => le_of_eq (norm_LSeries_term_line a c t n))
  exact h

/-- ‖L(a, c+it)‖ ≤ Σ' majorant. -/
theorem norm_LSeries_line_le (a : ℕ → ℂ) (c t : ℝ)
    (ha : Summable (fun N : ℕ => ‖a N‖ * (N : ℝ) ^ (-c))) :
    ‖LSeries a ((c:ℂ) + t * I)‖ ≤ ∑' n : ℕ, (if n = 0 then (0:ℝ) else ‖a n‖ * ((n:ℝ) ^ (-c))) := by
  have hs : Summable (fun n : ℕ => ‖LSeries.term a ((c:ℂ) + t * I) n‖) :=
    (summable_coeff_bound a c ha).congr fun n => (norm_LSeries_term_line a c t n).symm
  calc ‖LSeries a ((c:ℂ) + t * I)‖ = ‖∑' n, LSeries.term a ((c:ℂ) + t * I) n‖ := rfl
    _ ≤ ∑' n, ‖LSeries.term a ((c:ℂ) + t * I) n‖ := norm_tsum_le_tsum_norm hs
    _ = _ := tsum_congr fun n => norm_LSeries_term_line a c t n

/-- integrability of each term and summability of the L¹ norms (the domination for Step 3). -/
theorem line_terms_integrable {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (a : ℕ → ℂ) (c : ℝ) (ha : Summable (fun N : ℕ => ‖a N‖ * (N : ℝ) ^ (-c))) :
    (∀ n : ℕ, Integrable (fun t : ℝ => paperFT (tilt k (c - 1/2)) t
        * LSeries.term a ((c:ℂ) + t * I) n)) ∧
    Summable (fun n : ℕ => ∫ t : ℝ, ‖paperFT (tilt k (c - 1/2)) t
        * LSeries.term a ((c:ℂ) + t * I) n‖) := by
  have hkb2 : ContDiff ℝ 2 (tilt k (c - 1/2)) := tilt_contDiff hk _
  have hkbc : HasCompactSupport (tilt k (c - 1/2)) := tilt_hasCompactSupport hkc _
  have hFkb := Zeta23.EF.integrable_fourier_of_contDiff_two hkb2 hkbc
  have hpfi : Integrable (fun t : ℝ => paperFT (tilt k (c - 1/2)) t) :=
    Zeta23.EF.integrable_paperFT_ofReal hFkb
  have hcont : ∀ n : ℕ, Continuous (fun t : ℝ => LSeries.term a ((c:ℂ) + t * I) n) :=
    continuous_LSeries_term_line a c
  have hint : ∀ n : ℕ, Integrable (fun t : ℝ => paperFT (tilt k (c - 1/2)) t
      * LSeries.term a ((c:ℂ) + t * I) n) := by
    intro n
    refine hpfi.mul_bdd (c := if n = 0 then (0:ℝ) else ‖a n‖ * ((n:ℝ) ^ (-c)))
      (hcont n).aestronglyMeasurable ?_
    filter_upwards with t
    rw [norm_LSeries_term_line]
  have heval : ∀ n : ℕ, (∫ t : ℝ, ‖paperFT (tilt k (c - 1/2)) t
      * LSeries.term a ((c:ℂ) + t * I) n‖)
      = (∫ t : ℝ, ‖paperFT (tilt k (c - 1/2)) t‖)
        * (if n = 0 then (0:ℝ) else ‖a n‖ * ((n:ℝ) ^ (-c))) := by
    intro n
    rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [norm_mul, norm_LSeries_term_line]
  have hcn := summable_coeff_bound a c ha
  refine ⟨hint, ?_⟩
  refine ((hcn.mul_left (∫ t : ℝ, ‖paperFT (tilt k (c - 1/2)) t‖)).congr fun n => ?_)
  rw [heval n]

/-- Step 3 (tsum/integral swap). -/
theorem line_integral_swap_gen {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (a : ℕ → ℂ) (c : ℝ) (ha : Summable (fun N : ℕ => ‖a N‖ * (N : ℝ) ^ (-c))) :
    ∫ t : ℝ, (∑' n : ℕ, paperFT (tilt k (c - 1/2)) t * LSeries.term a (c + t * I) n)
      = ∑' n : ℕ, ∫ t : ℝ, paperFT (tilt k (c - 1/2)) t * LSeries.term a (c + t * I) n := by
  obtain ⟨hint, hsum⟩ := line_terms_integrable hk hkc a c ha
  exact (MeasureTheory.hasSum_integral_of_summable_integral_norm hint hsum).tsum_eq.symm

/-- integrability of H(c+it)·L(a, c+it) on the line. -/
theorem integrable_Hfn_mul_LSeries {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) (a : ℕ → ℂ) (c : ℝ)
    (ha : Summable (fun N : ℕ => ‖a N‖ * (N : ℝ) ^ (-c))) :
    Integrable (fun t : ℝ => Hfn k ((c : ℂ) + t * I) * LSeries a ((c : ℂ) + t * I)) := by
  have hkb2 : ContDiff ℝ 2 (tilt k (c - 1/2)) := tilt_contDiff hk _
  have hkbc : HasCompactSupport (tilt k (c - 1/2)) := tilt_hasCompactSupport hkc _
  have hFkb := Zeta23.EF.integrable_fourier_of_contDiff_two hkb2 hkbc
  have hpfi : Integrable (fun t : ℝ => paperFT (tilt k (c - 1/2)) t) :=
    Zeta23.EF.integrable_paperFT_ofReal hFkb
  have hpfi' : Integrable (fun t : ℝ => Hfn k ((c:ℂ) + t * I)) :=
    hpfi.congr (Filter.Eventually.of_forall fun t => (Hfn_line k c t).symm)
  refine hpfi'.mul_bdd (c := ∑' n : ℕ, (if n = 0 then (0:ℝ) else ‖a n‖ * ((n:ℝ) ^ (-c))))
    (continuous_LSeries_line a c ha).aestronglyMeasurable ?_
  filter_upwards with t
  exact norm_LSeries_line_le a c t ha

/-- **(EF3)**: (1/2π)∫_ℝ H(c+it)·Σ_N a_N N^{−(c+it)} dt = Σ_N a_N N^{−1/2} k(log N). -/
theorem dirichlet_line {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) (c : ℝ)
    (a : ℕ → ℂ) (ha : Summable (fun N : ℕ => ‖a N‖ * (N : ℝ) ^ (-c))) :
    Integrable (fun t : ℝ => Hfn k ((c : ℂ) + t * I) * LSeries a ((c : ℂ) + t * I)) ∧
    (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, Hfn k ((c : ℂ) + t * I) * LSeries a ((c : ℂ) + t * I))
      = ∑' N : ℕ, a N / ((Real.sqrt N : ℝ) : ℂ) * k (Real.log N) := by
  refine ⟨integrable_Hfn_mul_LSeries hk hkc a c ha, ?_⟩
  have h1 : ∀ t : ℝ, Hfn k (c + t * I) * LSeries a (c + t * I)
      = ∑' n : ℕ, paperFT (tilt k (c - 1/2)) t * LSeries.term a (c + t * I) n :=
    fun t => integrand_eq_tsum_gen k a c t
  calc (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, Hfn k (c + t * I) * LSeries a (c + t * I)
      = (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, ∑' n : ℕ, paperFT (tilt k (c - 1/2)) t
          * LSeries.term a (c + t * I) n := by
        rw [integral_congr_ae (Filter.Eventually.of_forall h1)]
    _ = (1 / (2 * Real.pi) : ℂ) * ∑' n : ℕ, ∫ t : ℝ, paperFT (tilt k (c - 1/2)) t
          * LSeries.term a (c + t * I) n := by
        rw [line_integral_swap_gen hk hkc a c ha]
    _ = ∑' n : ℕ, (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, paperFT (tilt k (c - 1/2)) t
          * LSeries.term a (c + t * I) n := by
        rw [← tsum_mul_left]
    _ = ∑' n : ℕ, a n / ((Real.sqrt n : ℝ) : ℂ) * k (Real.log n) :=
        tsum_congr fun n => per_n_line_integral_gen hk hkc a c n

/-- the mirrored weight: (1/2π)∫ H(1−c−it)·L(a,c+it) dt = Σ_N a_N N^{−1/2} k(−log N). -/
theorem dirichlet_line_mirror {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    (c : ℝ) (a : ℕ → ℂ) (ha : Summable (fun N : ℕ => ‖a N‖ * (N : ℝ) ^ (-c))) :
    Integrable (fun t : ℝ => Hfn k (1 - c - t * I) * LSeries a ((c : ℂ) + t * I)) ∧
    (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, Hfn k (1 - c - t * I) * LSeries a ((c : ℂ) + t * I))
      = ∑' N : ℕ, a N / ((Real.sqrt N : ℝ) : ℂ) * k (-Real.log N) := by
  have hkneg2 : ContDiff ℝ 2 (fun u : ℝ => k (-u)) := hk.comp contDiff_neg
  have hknegc : HasCompactSupport (fun u : ℝ => k (-u)) := hkc.comp_homeomorph (Homeomorph.neg ℝ)
  have heq : (fun t : ℝ => Hfn k (1 - c - t * I) * LSeries a ((c : ℂ) + t * I))
      = fun t : ℝ => Hfn (fun u => k (-u)) ((c : ℂ) + t * I) * LSeries a ((c : ℂ) + t * I) := by
    funext t
    rw [Zeta23.WeilEF.Hfn_mirror k c t]
  rw [heq]
  exact dirichlet_line hkneg2 hknegc c a ha

end XiPrime
end Zeta23
