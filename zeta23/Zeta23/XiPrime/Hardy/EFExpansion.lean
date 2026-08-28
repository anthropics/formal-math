/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Hardy/EFExpansion.lean — L₂ on the line Re s = c (9/8 ≤ c ≤ 5/4), the freeze, and the uniform line bounds
for the W explicit formula (template: Zeta23/XiPrime/ExplicitFormula/Expansion.lean §§3–7 with L ↦ L₂,
L⋆ ↦ L₂⋆ := ½log(τ/2π) (real: no phase), 5/4 ↦ c).

 X1 norm_L2_sub_L2star_self_le : ‖L₂(c+it) − L₂⋆(t)‖ ≤ C/t (t ≥ 2)  — one-point Stirling: L₂ = ½[Γℝ′/Γℝ(s) +
    Γℝ′/Γℝ(1−s)], the second shifted to 3−s (Hardy.logDeriv_Gammaℝ_shift); ψ(w) = log w − 1/(2w) + O(Im w)⁻² at
    w₁ = s/2 and w₂ = (3−s)/2, whose logarithms have phases → +π/2, −π/2 that cancel, leaving ½log(t/2) − ½log π.
 X2 norm_deriv_L2_le;  X3 norm_L2_sub_L2star_le, norm_L2_ge;  X4 norm_Afn_le_line, norm_Bfn_le_line;
 X5 freeze_on_line_W;  X6 frozen_uniform_W;  X7 derivE2_div_E2_uniform (+ continuity, conj);  X8 the F_𝒵 / E₂ line bounds.
-/
import Zeta23.XiPrime.Hardy.EFBasic
import Zeta23.XiPrime.Hardy.TwoLine

open Complex Set Filter Topology
open scoped ComplexConjugate ArithmeticFunction

noncomputable section

namespace Zeta23
namespace XiPrime
namespace Hardy

variable {c : ℝ}

/-! ## A. the line Re s = c -/

theorem re_line (c t : ℝ) : (((c : ℝ) : ℂ) + t * I).re = c := by simp
theorem im_line (c t : ℝ) : (((c : ℝ) : ℂ) + t * I).im = t := by simp

theorem one_lt_re_line (hc1 : 9/8 ≤ c) (t : ℝ) : 1 < (((c:ℝ):ℂ) + t * I).re := by rw [re_line]; linarith

theorem mem_goodStrip_line (hc1 : 9/8 ≤ c) (hc2 : c ≤ 5/4) (t : ℝ) : ((c:ℝ):ℂ) + t * I ∈ GoodStrip := by
  refine ⟨?_, ?_⟩ <;> rw [re_line] <;> linarith

theorem norm_line_ge (c t : ℝ) : |t| ≤ ‖((c:ℝ):ℂ) + t * I‖ := by
  have := Complex.abs_im_le_norm (((c:ℝ):ℂ) + t * I); simpa using this

theorem norm_line_sub_ge (c a t : ℝ) : |t| ≤ ‖((c:ℝ):ℂ) + t * I - (a:ℂ)‖ := by
  have := Complex.abs_im_le_norm (((c:ℝ):ℂ) + t * I - (a:ℂ)); simpa using this

theorem norm_sub_line_ge (c a t : ℝ) : |t| ≤ ‖(a:ℂ) - (((c:ℝ):ℂ) + t * I)‖ := by
  rw [norm_sub_rev]; exact norm_line_sub_ge c a t

theorem conj_line (c t : ℝ) : conj (((c:ℝ):ℂ) + t * I) = ((c:ℝ):ℂ) + (-t:ℝ) * I := by
  apply Complex.ext <;> simp

theorem continuous_line (c : ℝ) : Continuous (fun t : ℝ => ((c:ℝ):ℂ) + t * I) := by fun_prop

theorem norm_add₃_le' {a b d : ℂ} : ‖a + b + d‖ ≤ ‖a‖ + ‖b‖ + ‖d‖ :=
  (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)

/-! ## X4. Uniform bounds for A and B on the line -/

theorem norm_Afn_le_line (hc1 : 9/8 ≤ c) :
    ∃ A₀ : ℝ, 0 ≤ A₀ ∧ ∀ t : ℝ, ‖Afn (((c:ℝ):ℂ) + t * I)‖ ≤ A₀ := by
  obtain ⟨M, hM0, hM⟩ := Zeta23.WeilEF.norm_logDeriv_zeta_le_of_one_lt_re (c := c) (by linarith)
  refine ⟨M, hM0, fun t => ?_⟩
  have h := hM t
  rw [logDeriv_zeta_eq_neg_Afn (one_lt_re_line hc1 t), norm_neg] at h
  exact h

theorem norm_Bfn_le_line (hc1 : 9/8 ≤ c) :
    ∃ B₀ : ℝ, 0 ≤ B₀ ∧ ∀ t : ℝ, ‖Bfn (((c:ℝ):ℂ) + t * I)‖ ≤ B₀ := by
  have hc : 1 < ((c:ℝ):ℂ).re := by simp; linarith
  have hsum : Summable (fun n : ℕ => ‖LSeries.term (fun n => ((Λ n * Real.log n : ℝ) : ℂ)) ((c:ℝ):ℂ) n‖) :=
    summable_norm_iff.mpr (summable_Bfn hc)
  refine ⟨∑' n : ℕ, ‖LSeries.term (fun n => ((Λ n * Real.log n : ℝ) : ℂ)) ((c:ℝ):ℂ) n‖,
    tsum_nonneg fun _ => norm_nonneg _, fun t => ?_⟩
  have hnorm : ∀ n : ℕ, ‖LSeries.term (fun n => ((Λ n * Real.log n : ℝ) : ℂ)) (((c:ℝ):ℂ) + t * I) n‖
      = ‖LSeries.term (fun n => ((Λ n * Real.log n : ℝ) : ℂ)) ((c:ℝ):ℂ) n‖ := by
    intro n
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, re_line, Complex.ofReal_re]
  unfold Bfn LSeries
  calc ‖∑' n, LSeries.term (fun n => ((Λ n * Real.log n : ℝ) : ℂ)) (((c:ℝ):ℂ) + t * I) n‖
      ≤ ∑' n, ‖LSeries.term (fun n => ((Λ n * Real.log n : ℝ) : ℂ)) (((c:ℝ):ℂ) + t * I) n‖ :=
        norm_tsum_le_tsum_norm (by simp_rw [hnorm]; exact hsum)
    _ = _ := by simp_rw [hnorm]

/-! ## X1. One-point Stirling for L₂ on the line -/

section stirling
open Real in
/-- the complex logarithm near the positive imaginary axis, general abscissa 0 < a ≤ 1:
‖log(a + i t/2) − (log(t/2) + iπ/2)‖ ≤ 6/t for t ≥ 2. -/
theorem norm_log_sub_le_gen {a t : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (ht : 2 ≤ t) :
    ‖Complex.log (((a:ℝ):ℂ) + ((t/2:ℝ):ℂ) * I)
        - (((Real.log (t/2) : ℝ) : ℂ) + ((Real.pi/2 : ℝ) : ℂ) * I)‖ ≤ 6 / t := by
  set w : ℂ := ((a:ℝ):ℂ) + ((t/2:ℝ):ℂ) * I with hw
  have hwre : w.re = a := by simp [hw]
  have hwim : w.im = t/2 := by simp [hw]
  have ht0 : 0 < t := by linarith
  have ht2 : 0 < t/2 := by linarith
  have hnorm_sq : ‖w‖ ^ 2 = a^2 + (t/2)^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hwre, hwim]; ring
  have hnorm_ge : t/2 ≤ ‖w‖ := by
    have := Complex.abs_im_le_norm w
    rw [hwim, abs_of_pos ht2] at this
    exact this
  have hnorm_pos : 0 < ‖w‖ := lt_of_lt_of_le ht2 hnorm_ge
  have hnorm_le : ‖w‖ ≤ a + t/2 := by
    calc ‖w‖ ≤ ‖((a:ℝ):ℂ)‖ + ‖((t/2:ℝ):ℂ) * I‖ := norm_add_le _ _
      _ = a + t/2 := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos ha0, abs_of_pos ht2]
  -- the difference, componentwise
  have hre : (Complex.log w - (((Real.log (t/2) : ℝ) : ℂ) + ((Real.pi/2 : ℝ) : ℂ) * I)).re
      = Real.log ‖w‖ - Real.log (t/2) := by
    simp [Complex.log_re]
  have him : (Complex.log w - (((Real.log (t/2) : ℝ) : ℂ) + ((Real.pi/2 : ℝ) : ℂ) * I)).im
      = Complex.arg w - Real.pi/2 := by
    simp [Complex.log_im]
  -- real part: 0 ≤ log‖w‖ − log(t/2) ≤ 2a/t ≤ 2/t
  have hre_bd : |Real.log ‖w‖ - Real.log (t/2)| ≤ 2 / t := by
    have h1 : 0 ≤ Real.log ‖w‖ - Real.log (t/2) := by
      have := Real.log_le_log ht2 hnorm_ge
      linarith
    rw [abs_of_nonneg h1, ← Real.log_div hnorm_pos.ne' ht2.ne']
    have h2 : Real.log (‖w‖ / (t/2)) ≤ ‖w‖ / (t/2) - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h3 : ‖w‖ / (t/2) - 1 ≤ 2 / t := by
      have : ‖w‖ / (t/2) ≤ (a + t/2) / (t/2) := div_le_div_of_nonneg_right hnorm_le ht2.le
      have e : (a + t/2) / (t/2) = 2 * a / t + 1 := by field_simp
      have e2 : 2 * a / t ≤ 2 / t := by rw [div_le_div_iff₀ ht0 ht0]; nlinarith
      linarith
    exact h2.trans h3
  -- imaginary part: 0 ≤ π/2 − arg w ≤ 4a/t ≤ 4/t
  have him_bd : |Complex.arg w - Real.pi/2| ≤ 4 / t := by
    have harg : Complex.arg w = Real.arcsin (w.im / ‖w‖) :=
      Complex.arg_of_re_nonneg (by rw [hwre]; exact ha0.le)
    set u : ℝ := w.im / ‖w‖ with hu
    have hu0 : 0 ≤ u := by rw [hu, hwim]; positivity
    have hu1 : u ≤ 1 := by
      rw [hu, div_le_one hnorm_pos, hwim]; exact hnorm_ge
    set v : ℝ := Real.pi/2 - Real.arcsin u with hv
    have hv0 : 0 ≤ v := by
      have := Real.arcsin_le_pi_div_two u
      rw [hv]; linarith
    have hv1 : v ≤ Real.pi/2 := by
      have : 0 ≤ Real.arcsin u := Real.arcsin_nonneg.mpr hu0
      rw [hv]; linarith
    have hsinv : Real.sin v = Real.sqrt (1 - u ^ 2) := by
      rw [hv, ← Real.arccos_eq_pi_div_two_sub_arcsin, Real.sin_arccos]
    have hsqrt : Real.sqrt (1 - u ^ 2) = a / ‖w‖ := by
      have e : 1 - u ^ 2 = (a / ‖w‖) ^ 2 := by
        rw [hu, hwim, div_pow, div_pow]
        field_simp
        nlinarith [hnorm_sq]
      rw [e, Real.sqrt_sq (by positivity)]
    have hjordan : 2 / Real.pi * v ≤ Real.sin v := Real.mul_le_sin hv0 hv1
    have hvle : v ≤ Real.pi / 2 * (a / ‖w‖) := by
      rw [hsinv, hsqrt] at hjordan
      have hπ := Real.pi_pos
      have : v = Real.pi / 2 * (2 / Real.pi * v) := by field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_left hjordan (by positivity)
    have hfin : Real.pi / 2 * (a / ‖w‖) ≤ 4 / t := by
      have hπ4 : Real.pi ≤ 4 := Real.pi_le_four
      have h1 : a / ‖w‖ ≤ a / (t/2) := div_le_div_of_nonneg_left ha0.le ht2 hnorm_ge
      calc Real.pi / 2 * (a / ‖w‖) ≤ 4 / 2 * (a / (t/2)) := by
            exact mul_le_mul (by linarith) h1 (by positivity) (by norm_num)
        _ = 4 * a / t := by field_simp
        _ ≤ 4 / t := by rw [div_le_div_iff₀ ht0 ht0]; nlinarith
    rw [harg, show Real.arcsin u - Real.pi / 2 = -v by rw [hv]; ring, abs_neg, abs_of_nonneg hv0]
    exact hvle.trans hfin
  -- combine
  calc ‖Complex.log w - (((Real.log (t/2) : ℝ) : ℂ) + ((Real.pi/2 : ℝ) : ℂ) * I)‖
      ≤ |(Complex.log w - (((Real.log (t/2) : ℝ) : ℂ) + ((Real.pi/2 : ℝ) : ℂ) * I)).re|
        + |(Complex.log w - (((Real.log (t/2) : ℝ) : ℂ) + ((Real.pi/2 : ℝ) : ℂ) * I)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 / t + 4 / t := by rw [hre, him]; exact add_le_add hre_bd him_bd
    _ = 6 / t := by ring


/-- the twin near the NEGATIVE imaginary axis: ‖log(a − i t/2) − (log(t/2) − iπ/2)‖ ≤ 6/t. -/
theorem norm_log_sub_le_gen_neg {a t : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) (ht : 2 ≤ t) :
    ‖Complex.log (((a:ℝ):ℂ) - ((t/2:ℝ):ℂ) * I)
        - (((Real.log (t/2) : ℝ) : ℂ) - ((Real.pi/2 : ℝ) : ℂ) * I)‖ ≤ 6 / t := by
  have h := norm_log_sub_le_gen ha0 ha1 ht
  set z : ℂ := ((a:ℝ):ℂ) + ((t/2:ℝ):ℂ) * I with hz
  have harg : z.arg ≠ Real.pi := by
    have : 0 ≤ z.re := by simp [hz]; exact ha0.le
    have h1 := Complex.arg_le_pi_div_two_iff.mpr (Or.inl this)
    intro h2; rw [h2] at h1; linarith [Real.pi_pos]
  have hconj : conj z = ((a:ℝ):ℂ) - ((t/2:ℝ):ℂ) * I := by
    rw [hz, map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]; ring
  have hlog : Complex.log (conj z) = conj (Complex.log z) := by
    rw [Complex.log_conj_eq_ite, if_neg harg]
  rw [← hconj, hlog]
  have e : (((Real.log (t/2) : ℝ) : ℂ) - ((Real.pi/2 : ℝ) : ℂ) * I)
      = conj (((Real.log (t/2) : ℝ) : ℂ) + ((Real.pi/2 : ℝ) : ℂ) * I) := by
    rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]; ring
  rw [e, ← map_sub, Complex.norm_conj]
  exact h

/-- the explicit form of L₂ on Re s ∈ (1, 3/2), off the real axis:
L₂(s) = −log π/2 + ¼ψ(s/2) + ¼ψ((3−s)/2) − 1/(2(1−s)). -/
theorem L2_eq_digamma_shift {s : ℂ} (hs : s ∈ GoodStrip) (him : s.im ≠ 0) :
    L2 s = -(Real.log Real.pi : ℂ) / 2 + (1/4 : ℂ) * Complex.digamma (s / 2)
      + (1/4 : ℂ) * Complex.digamma ((3 - s) / 2) - (1/2 : ℂ) / (1 - s) := by
  have hu : (1 - s).im ≠ 0 := im_one_sub_ne_zero him
  rw [L2_eq him, logDeriv_Gammaℝ_shift hu, show (1:ℂ) - s + 2 = 3 - s by ring,
    Zeta23.RvM.logDeriv_Gammaℝ (by exact lt_trans zero_lt_one hs.1),
    Zeta23.RvM.logDeriv_Gammaℝ (by simp; linarith [hs.2])]
  ring

/-- **X1. one-point Stirling for L₂**: ‖L₂(c+it) − L₂⋆(t)‖ ≤ 12/t for t ≥ 2  (L₂⋆(t) = ½log(t/2π), real). -/
theorem norm_L2_sub_L2star_self_le' (hc1 : 9/8 ≤ c) (hc2 : c ≤ 5/4) {t : ℝ} (ht : 2 ≤ t) :
    ‖L2 (((c:ℝ):ℂ) + t * I) - ((L2star t : ℝ) : ℂ)‖ ≤ 12 / t := by
  have ht0 : 0 < t := by linarith
  set s : ℂ := ((c:ℝ):ℂ) + t * I with hs
  have hsG : s ∈ GoodStrip := mem_goodStrip_line hc1 hc2 t
  have hsim : s.im ≠ 0 := by rw [hs, im_line]; exact ht0.ne'
  -- the two Stirling points
  set w₁ : ℂ := (((c/2:ℝ)):ℂ) + ((t/2:ℝ):ℂ) * I with hw₁
  set w₂ : ℂ := ((((3-c)/2:ℝ)):ℂ) - ((t/2:ℝ):ℂ) * I with hw₂
  have hsw₁ : s / 2 = w₁ := by simp [hs, hw₁]; ring
  have hsw₂ : (3 - s) / 2 = w₂ := by simp [hs, hw₂]; ring
  have hw₁re : 0 < w₁.re := by simp [hw₁]; linarith
  have hw₂re : 0 < w₂.re := by simp [hw₂]; linarith
  have hw₁im : w₁.im = t/2 := by simp [hw₁]
  have hw₂im : w₂.im = -(t/2) := by simp [hw₂]
  have hw₁im' : 1/2 ≤ |w₁.im| := by rw [hw₁im, abs_of_pos (by linarith)]; linarith
  have hw₂im' : 1/2 ≤ |w₂.im| := by rw [hw₂im, abs_neg, abs_of_pos (by linarith)]; linarith
  have hst₁ : ‖Complex.digamma w₁ - Complex.log w₁ + (1/2 : ℂ) / w₁‖ ≤ 6 / t := by
    refine (Zeta23.StirlingVert.digamma_stirling hw₁re hw₁im').trans ?_
    rw [hw₁im, div_le_div_iff₀ (by positivity) ht0]; nlinarith
  have hst₂ : ‖Complex.digamma w₂ - Complex.log w₂ + (1/2 : ℂ) / w₂‖ ≤ 6 / t := by
    refine (Zeta23.StirlingVert.digamma_stirling hw₂re hw₂im').trans ?_
    rw [hw₂im, neg_sq, div_le_div_iff₀ (by positivity) ht0]; nlinarith
  have hlog₁ := norm_log_sub_le_gen (a := c/2) (by linarith) (by linarith) ht
  have hlog₂ := norm_log_sub_le_gen_neg (a := (3-c)/2) (by linarith) (by linarith) ht
  -- reciprocals are O(1/t)
  have hw₁inv : ‖w₁⁻¹‖ ≤ (t/2)⁻¹ := by
    rw [norm_inv]; refine inv_anti₀ (by positivity) ?_
    have := Complex.abs_im_le_norm w₁; rwa [hw₁im, abs_of_pos (by positivity)] at this
  have hw₂inv : ‖w₂⁻¹‖ ≤ (t/2)⁻¹ := by
    rw [norm_inv]; refine inv_anti₀ (by positivity) ?_
    have := Complex.abs_im_le_norm w₂; rwa [hw₂im, abs_neg, abs_of_pos (by positivity)] at this
  have hsinv : ‖(1 - s)⁻¹‖ ≤ t⁻¹ := by
    rw [norm_inv]; refine inv_anti₀ ht0 ?_
    have := Complex.abs_im_le_norm (1 - s)
    rw [hs] at this; simp at this; rwa [abs_of_pos ht0] at this
  -- the decomposition
  have hL : L2 s = -(Real.log Real.pi : ℂ) / 2 + (1/4 : ℂ) * Complex.digamma w₁
      + (1/4 : ℂ) * Complex.digamma w₂ - (1/2 : ℂ) / (1 - s) := by
    rw [L2_eq_digamma_shift hsG hsim, hsw₁, hsw₂]
  have hstar : ((L2star t : ℝ) : ℂ)
      = (1/4 : ℂ) * ((((Real.log (t/2) : ℝ) : ℂ) + ((Real.pi/2 : ℝ) : ℂ) * I)
          + (((Real.log (t/2) : ℝ) : ℂ) - ((Real.pi/2 : ℝ) : ℂ) * I))
        - (Real.log Real.pi : ℂ) / 2 := by
    unfold L2star
    have e1 : Real.log (t / (2 * Real.pi)) = Real.log (t/2) - Real.log Real.pi := by
      rw [show t / (2 * Real.pi) = (t/2) / Real.pi by ring, Real.log_div (by positivity) Real.pi_pos.ne']
    rw [e1]; push_cast; ring
  have key : L2 s - ((L2star t : ℝ) : ℂ)
      = (1/4 : ℂ) * (Complex.digamma w₁ - Complex.log w₁ + (1/2 : ℂ) / w₁)
        + (1/4 : ℂ) * (Complex.digamma w₂ - Complex.log w₂ + (1/2 : ℂ) / w₂)
        + ((1/4 : ℂ) * (Complex.log w₁ - (((Real.log (t/2) : ℝ) : ℂ) + ((Real.pi/2 : ℝ) : ℂ) * I))
          + (1/4 : ℂ) * (Complex.log w₂ - (((Real.log (t/2) : ℝ) : ℂ) - ((Real.pi/2 : ℝ) : ℂ) * I))
          + (-(1/8 : ℂ) * w₁⁻¹ - (1/8 : ℂ) * w₂⁻¹ - (1/2 : ℂ) * (1 - s)⁻¹)) := by
    rw [hL, hstar]; simp only [div_eq_mul_inv]; ring
  rw [key]
  have n14 : ‖(1/4 : ℂ)‖ = 1/4 := by norm_num
  have n18 : ‖(1/8 : ℂ)‖ = 1/8 := by norm_num
  have n12 : ‖(1/2 : ℂ)‖ = 1/2 := by norm_num
  have hrest : ‖-(1/8 : ℂ) * w₁⁻¹ - (1/8 : ℂ) * w₂⁻¹ - (1/2 : ℂ) * (1 - s)⁻¹‖
      ≤ (1/8) * (t/2)⁻¹ + (1/8) * (t/2)⁻¹ + (1/2) * t⁻¹ := by
    calc ‖-(1/8 : ℂ) * w₁⁻¹ - (1/8 : ℂ) * w₂⁻¹ - (1/2 : ℂ) * (1 - s)⁻¹‖
        ≤ ‖-(1/8 : ℂ) * w₁⁻¹‖ + ‖(1/8 : ℂ) * w₂⁻¹‖ + ‖(1/2 : ℂ) * (1 - s)⁻¹‖ := norm_sub₃_le'
      _ ≤ (1/8) * (t/2)⁻¹ + (1/8) * (t/2)⁻¹ + (1/2) * t⁻¹ := by
          rw [norm_mul, norm_neg, n18, norm_mul, n18, norm_mul, n12]
          gcongr
  calc ‖(1/4 : ℂ) * (Complex.digamma w₁ - Complex.log w₁ + (1/2 : ℂ) / w₁)
        + (1/4 : ℂ) * (Complex.digamma w₂ - Complex.log w₂ + (1/2 : ℂ) / w₂)
        + ((1/4 : ℂ) * (Complex.log w₁ - (((Real.log (t/2) : ℝ) : ℂ) + ((Real.pi/2 : ℝ) : ℂ) * I))
          + (1/4 : ℂ) * (Complex.log w₂ - (((Real.log (t/2) : ℝ) : ℂ) - ((Real.pi/2 : ℝ) : ℂ) * I))
          + (-(1/8 : ℂ) * w₁⁻¹ - (1/8 : ℂ) * w₂⁻¹ - (1/2 : ℂ) * (1 - s)⁻¹))‖
      ≤ ‖(1/4 : ℂ) * (Complex.digamma w₁ - Complex.log w₁ + (1/2 : ℂ) / w₁)‖
        + ‖(1/4 : ℂ) * (Complex.digamma w₂ - Complex.log w₂ + (1/2 : ℂ) / w₂)‖
        + (‖(1/4 : ℂ) * (Complex.log w₁ - (((Real.log (t/2) : ℝ) : ℂ) + ((Real.pi/2 : ℝ) : ℂ) * I))‖
          + ‖(1/4 : ℂ) * (Complex.log w₂ - (((Real.log (t/2) : ℝ) : ℂ) - ((Real.pi/2 : ℝ) : ℂ) * I))‖
          + ‖-(1/8 : ℂ) * w₁⁻¹ - (1/8 : ℂ) * w₂⁻¹ - (1/2 : ℂ) * (1 - s)⁻¹‖) :=
        norm_add₃_le'.trans (add_le_add le_rfl norm_add₃_le')
    _ ≤ (1/4) * (6/t) + (1/4) * (6/t) + ((1/4) * (6/t) + (1/4) * (6/t)
          + ((1/8) * (t/2)⁻¹ + (1/8) * (t/2)⁻¹ + (1/2) * t⁻¹)) := by
        rw [norm_mul, norm_mul, norm_mul, norm_mul, n14]
        gcongr
    _ = 7 / t := by field_simp; ring
    _ ≤ 12 / t := by rw [div_le_div_iff₀ ht0 ht0]; nlinarith

/-- X1 in ∃-form: ‖L₂(c+it) − L₂⋆(t)‖ ≤ C/t for t ≥ 2. -/
theorem norm_L2_sub_L2star_self_le (hc1 : 9/8 ≤ c) (hc2 : c ≤ 5/4) :
    ∃ C : ℝ, ∀ t : ℝ, 2 ≤ t → ‖L2 (((c:ℝ):ℂ) + t * I) - ((L2star t : ℝ) : ℂ)‖ ≤ C / t :=
  ⟨12, fun _ ht => norm_L2_sub_L2star_self_le' hc1 hc2 ht⟩

end stirling

/-! ## X2. L₂′ on the line -/

section derivL2

/-- the explicit digamma form of L₂ (right side of L2_eq_digamma_shift), for differentiation. -/
def L2D (s : ℂ) : ℂ :=
  -(Real.log Real.pi : ℂ) / 2 + (1/4 : ℂ) * Complex.digamma (s / 2)
    + (1/4 : ℂ) * Complex.digamma ((3 - s) / 2) - (1/2 : ℂ) / (1 - s)

theorem isOpen_goodStrip_off : IsOpen (GoodStrip ∩ {s : ℂ | s.im ≠ 0}) := isOpen_goodStrip.inter isOpen_im_ne_zero

theorem L2_eventuallyEq_L2D {s : ℂ} (hs : s ∈ GoodStrip) (him : s.im ≠ 0) : L2 =ᶠ[𝓝 s] L2D := by
  filter_upwards [isOpen_goodStrip_off.mem_nhds ⟨hs, him⟩] with z hz
  exact L2_eq_digamma_shift hz.1 hz.2

theorem hasDerivAt_L2D {s : ℂ} (hs1 : s ≠ 1) (hsi : (s / 2).im ≠ 0) (hsi' : ((3 - s) / 2).im ≠ 0) :
    HasDerivAt L2D ((1/8 : ℂ) * deriv Complex.digamma (s / 2) - (1/8 : ℂ) * deriv Complex.digamma ((3 - s) / 2)
      - (1/2 : ℂ) * ((1 - s) ^ 2)⁻¹) s := by
  have hmem := mem_integerComplement_of_im_ne_zero hsi
  have hmem' := mem_integerComplement_of_im_ne_zero hsi'
  have hψ : HasDerivAt (fun z => Complex.digamma (z / 2)) (deriv Complex.digamma (s / 2) * (1 / 2)) s := by
    have h1 := (Zeta23.Stirling.differentiableAt_digamma hmem).hasDerivAt
    have h2 : HasDerivAt (fun z : ℂ => z / 2) (1 / 2) s := by
      simpa using (hasDerivAt_id s).div_const (2:ℂ)
    exact h1.comp s h2
  have hψ' : HasDerivAt (fun z => Complex.digamma ((3 - z) / 2)) (deriv Complex.digamma ((3 - s) / 2) * (-(1 / 2))) s := by
    have h1 := (Zeta23.Stirling.differentiableAt_digamma hmem').hasDerivAt
    have h2 : HasDerivAt (fun z : ℂ => (3 - z) / 2) (-(1 / 2)) s := by
      have := ((hasDerivAt_const s (3:ℂ)).fun_sub (hasDerivAt_id s)).div_const (2:ℂ)
      exact this.congr_deriv (by ring)
    exact h1.comp s h2
  have hinv1 : HasDerivAt (fun z : ℂ => (1/2 : ℂ) / (1 - z)) ((1/2 : ℂ) * ((1 - s) ^ 2)⁻¹) s := by
    have hne : (1 - s) ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
    have h := (hasDerivAt_inv hne).comp s ((hasDerivAt_const s (1:ℂ)).fun_sub (hasDerivAt_id s))
    have h' : HasDerivAt (fun z : ℂ => (1 - z)⁻¹) (((1 - s) ^ 2)⁻¹) s := by
      refine h.congr_deriv ?_; simp
    have := h'.const_mul (1/2 : ℂ)
    simpa [div_eq_mul_inv] using this
  have := (((hasDerivAt_const s (-(Real.log Real.pi : ℂ) / 2)).add (hψ.const_mul (1/4 : ℂ))).add
    (hψ'.const_mul (1/4 : ℂ))).sub hinv1
  exact this.congr_deriv (by ring)

theorem deriv_L2_eq {s : ℂ} (hs : s ∈ GoodStrip) (hsi : s.im ≠ 0) :
    deriv L2 s = (1/8 : ℂ) * deriv Complex.digamma (s / 2) - (1/8 : ℂ) * deriv Complex.digamma ((3 - s) / 2)
      - (1/2 : ℂ) * ((1 - s) ^ 2)⁻¹ := by
  have hs1 : s ≠ 1 := goodStrip_ne_one hs
  have hsi2 : (s / 2).im ≠ 0 := by rw [Complex.div_ofNat_im]; exact div_ne_zero hsi two_ne_zero
  have hsi3 : ((3 - s) / 2).im ≠ 0 := by
    rw [Complex.div_ofNat_im]; refine div_ne_zero ?_ two_ne_zero; simpa using hsi
  rw [(L2_eventuallyEq_L2D hs hsi).deriv_eq]
  exact (hasDerivAt_L2D hs1 hsi2 hsi3).deriv

/-- **X2. L₂′ on the line**: ‖L₂′(c+it)‖ ≤ 4/|t| for |t| ≥ 2. -/
theorem norm_deriv_L2_le' (hc1 : 9/8 ≤ c) (hc2 : c ≤ 5/4) {t : ℝ} (ht : 2 ≤ |t|) :
    ‖deriv L2 (((c:ℝ):ℂ) + t * I)‖ ≤ 4 / |t| := by
  set s : ℂ := ((c:ℝ):ℂ) + t * I with hs
  have ht0 : 0 < |t| := by linarith
  have htne : t ≠ 0 := abs_pos.mp ht0
  have hsim : s.im = t := by simp [hs]
  rw [deriv_L2_eq (mem_goodStrip_line hc1 hc2 t) (by rwa [hsim])]
  -- the two trigamma terms
  have hw₁ : 0 < (s / 2).re := by rw [Complex.div_ofNat_re, hs, re_line]; linarith
  have hw₁im : (s / 2).im = t / 2 := by rw [Complex.div_ofNat_im, hsim]
  have hw₁i : 1/2 ≤ |(s / 2).im| := by rw [hw₁im, abs_div, abs_two]; linarith
  have hw₂ : 0 < ((3 - s) / 2).re := by rw [Complex.div_ofNat_re]; simp [hs]; linarith
  have hw₂im : ((3 - s) / 2).im = -(t / 2) := by rw [Complex.div_ofNat_im]; simp [hs]; ring
  have hw₂i : 1/2 ≤ |((3 - s) / 2).im| := by rw [hw₂im, abs_neg, abs_div, abs_two]; linarith
  have hψ₁ := norm_deriv_digamma_le hw₁ hw₁i
  have hψ₂ := norm_deriv_digamma_le hw₂ hw₂i
  rw [hw₁im, abs_div, abs_two] at hψ₁
  rw [hw₂im, neg_sq, abs_neg, abs_div, abs_two] at hψ₂
  have hinv : ‖((1 - s) ^ 2)⁻¹‖ ≤ (|t| ^ 2)⁻¹ := by
    rw [norm_inv, norm_pow]
    refine inv_anti₀ (by positivity) (pow_le_pow_left₀ (abs_nonneg t) ?_ 2)
    have := Complex.abs_im_le_norm (1 - s); rw [hs] at this; simpa using this
  have htt : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
  have n18 : ‖(1/8 : ℂ)‖ = 1/8 := by norm_num
  have n12 : ‖(1/2 : ℂ)‖ = 1/2 := by norm_num
  calc ‖(1/8 : ℂ) * deriv Complex.digamma (s / 2) - (1/8 : ℂ) * deriv Complex.digamma ((3 - s) / 2)
        - (1/2 : ℂ) * ((1 - s) ^ 2)⁻¹‖
      ≤ ‖(1/8 : ℂ) * deriv Complex.digamma (s / 2)‖ + ‖(1/8 : ℂ) * deriv Complex.digamma ((3 - s) / 2)‖
        + ‖(1/2 : ℂ) * ((1 - s) ^ 2)⁻¹‖ := norm_sub₃_le'
    _ ≤ (1/8) * (1 / (t/2) ^ 2 + 2 / (|t| / 2)) + (1/8) * (1 / (t/2) ^ 2 + 2 / (|t| / 2))
        + (1/2) * (|t| ^ 2)⁻¹ := by
        rw [norm_mul, norm_mul, norm_mul, n18, n12]
        gcongr
    _ = 3 / (2 * |t| ^ 2) + 1 / |t| := by
        have e : (t / 2) ^ 2 = |t| ^ 2 / 4 := by rw [div_pow, htt]; norm_num
        rw [e]; field_simp; ring
    _ ≤ 4 / |t| := by
        rw [div_add_div _ _ (by positivity) ht0.ne', div_le_div_iff₀ (by positivity) ht0]
        nlinarith

theorem norm_deriv_L2_le (hc1 : 9/8 ≤ c) (hc2 : c ≤ 5/4) :
    ∃ C : ℝ, ∀ t : ℝ, 2 ≤ |t| → ‖deriv L2 (((c:ℝ):ℂ) + t * I)‖ ≤ C / |t| :=
  ⟨4, fun _ ht => norm_deriv_L2_le' hc1 hc2 ht⟩

end derivL2

/-! ## X3. L₂ against a frozen L₂⋆(τ), and the lower bound for ‖L₂‖ -/

section frozen

/-- ‖L₂⋆(t) − L₂⋆(τ)‖ = ½|log t − log τ| ≤ |t−τ|/(2 min t τ). -/
theorem norm_L2star_sub_L2star_le {t τ : ℝ} (ht : 0 < t) (hτ : 0 < τ) :
    ‖((L2star t : ℝ) : ℂ) - ((L2star τ : ℝ) : ℂ)‖ ≤ |t - τ| / (2 * min t τ) := by
  have e : ((L2star t : ℝ) : ℂ) - ((L2star τ : ℝ) : ℂ) = (((Real.log t - Real.log τ) / 2 : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sub]; congr 1
    unfold L2star
    rw [Real.log_div ht.ne' (by positivity), Real.log_div hτ.ne' (by positivity)]; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_two]
  have := abs_log_sub_log_le ht hτ
  have hm : 0 < min t τ := lt_min ht hτ
  rw [div_le_div_iff₀ two_pos (by positivity)]
  calc |Real.log t - Real.log τ| * (2 * min t τ) = 2 * (|Real.log t - Real.log τ| * min t τ) := by ring
    _ ≤ 2 * |t - τ| := by
        have := (le_div_iff₀ hm).mp this
        linarith
    _ = |t - τ| * 2 := by ring

/-- **X3a. L₂ against a frozen L₂⋆(τ)**: ‖L₂(c+it) − L₂⋆(τ)‖ ≤ (|t−τ| + 24)/(2 min t τ) for t, τ ≥ 2. -/
theorem norm_L2_sub_L2star_le' (hc1 : 9/8 ≤ c) (hc2 : c ≤ 5/4) {t τ : ℝ} (ht : 2 ≤ t) (hτ : 2 ≤ τ) :
    ‖L2 (((c:ℝ):ℂ) + t * I) - ((L2star τ : ℝ) : ℂ)‖ ≤ (|t - τ| + 24) / (2 * min t τ) := by
  have ht0 : 0 < t := by linarith
  have hτ0 : 0 < τ := by linarith
  have hm : 0 < min t τ := lt_min ht0 hτ0
  have h1 := norm_L2_sub_L2star_self_le' hc1 hc2 ht
  have h2 := norm_L2star_sub_L2star_le ht0 hτ0
  calc ‖L2 (((c:ℝ):ℂ) + t * I) - ((L2star τ : ℝ) : ℂ)‖
      ≤ ‖L2 (((c:ℝ):ℂ) + t * I) - ((L2star t : ℝ) : ℂ)‖ + ‖((L2star t : ℝ) : ℂ) - ((L2star τ : ℝ) : ℂ)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 12 / t + |t - τ| / (2 * min t τ) := add_le_add h1 h2
    _ ≤ 24 / (2 * min t τ) + |t - τ| / (2 * min t τ) := by
        have : 12 / t ≤ 24 / (2 * min t τ) := by
          rw [div_le_div_iff₀ ht0 (by positivity)]
          nlinarith [min_le_left t τ]
        linarith
    _ = (|t - τ| + 24) / (2 * min t τ) := by ring

theorem norm_L2_sub_L2star_le (hc1 : 9/8 ≤ c) (hc2 : c ≤ 5/4) :
    ∃ C : ℝ, ∀ t τ : ℝ, 2 ≤ t → 2 ≤ τ →
      ‖L2 (((c:ℝ):ℂ) + t * I) - ((L2star τ : ℝ) : ℂ)‖ ≤ C * (|t - τ| + 1) / min t τ := by
  refine ⟨12, fun t τ ht hτ => (norm_L2_sub_L2star_le' hc1 hc2 ht hτ).trans ?_⟩
  have hm : 0 < min t τ := lt_min (by linarith) (by linarith)
  rw [div_le_div_iff₀ (by positivity) hm]
  nlinarith [abs_nonneg (t - τ)]

theorem log_two_pi_le_two' : Real.log (2 * Real.pi) ≤ 2 := log_two_pi_le_two

/-- ‖L₂⋆(τ)‖ ≥ ½log τ − 1 for τ > 0. -/
theorem norm_L2star_ge {τ : ℝ} (hτ : 0 < τ) : Real.log τ / 2 - 1 ≤ ‖((L2star τ : ℝ) : ℂ)‖ := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  unfold L2star
  rw [Real.log_div hτ.ne' (by positivity)]
  have := le_abs_self ((Real.log τ - Real.log (2 * Real.pi)) / 2)
  linarith [log_two_pi_le_two]

/-- ‖L₂(c+it)‖ ≥ ½log t − 7 for t ≥ 2. -/
theorem norm_L2_ge_pos (hc1 : 9/8 ≤ c) (hc2 : c ≤ 5/4) {t : ℝ} (ht : 2 ≤ t) :
    Real.log t / 2 - 7 ≤ ‖L2 (((c:ℝ):ℂ) + t * I)‖ := by
  have ht0 : 0 < t := by linarith
  have h1 := norm_L2_sub_L2star_self_le' hc1 hc2 ht
  have h2 := norm_L2star_ge ht0
  have h3 := norm_sub_norm_le (((L2star t : ℝ) : ℂ)) (L2 (((c:ℝ):ℂ) + t * I))
  rw [norm_sub_rev] at h3
  have h12 : 12 / t ≤ 6 := by rw [div_le_iff₀ ht0]; linarith
  linarith

/-- **X3b.** ‖L₂(c+it)‖ ≥ ½log|t| − 7 for |t| ≥ 2 (t < 0 by conjugation). -/
theorem norm_L2_ge' (hc1 : 9/8 ≤ c) (hc2 : c ≤ 5/4) {t : ℝ} (ht : 2 ≤ |t|) :
    Real.log |t| / 2 - 7 ≤ ‖L2 (((c:ℝ):ℂ) + t * I)‖ := by
  rcases le_or_gt 0 t with h | h
  · rw [abs_of_nonneg h] at ht ⊢; exact norm_L2_ge_pos hc1 hc2 ht
  · have ht' : 2 ≤ -t := by rwa [abs_of_neg h] at ht
    have him : (((c:ℝ):ℂ) + (-t:ℝ) * I).im ≠ 0 := by rw [im_line]; linarith
    have e : ((c:ℝ):ℂ) + t * I = conj (((c:ℝ):ℂ) + (-t:ℝ) * I) := by
      rw [conj_line]; simp
    rw [e, L2_conj him, Complex.norm_conj, abs_of_neg h]
    exact norm_L2_ge_pos hc1 hc2 ht'

theorem norm_L2_ge (hc1 : 9/8 ≤ c) (hc2 : c ≤ 5/4) :
    ∃ C : ℝ, ∀ t : ℝ, 2 ≤ |t| → Real.log |t| / 2 - C ≤ ‖L2 (((c:ℝ):ℂ) + t * I)‖ :=
  ⟨7, fun _ ht => norm_L2_ge' hc1 hc2 ht⟩

end frozen

/-! ## The archimedean line data for W: (c, L₂, L₂⋆) — instance of ExplicitFormula/Expansion §G -/

/-- ‖L₂(c+it)‖ ≤ M·log(2+|t|) for all real t. -/
theorem norm_L2_line (hc1 : 9/8 ≤ c) (hc2 : c ≤ 5/4) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, ‖L2 (((c:ℝ):ℂ) + t * I)‖ ≤ M * Real.log (2 + |t|) := by
  -- compact middle
  have hcont : Continuous (fun t : ℝ => L2 (((c:ℝ):ℂ) + t * I)) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    exact ((L2_analyticAt_goodStrip (mem_goodStrip_line hc1 hc2 t)).continuousAt).comp_of_eq
      (continuous_line c).continuousAt rfl
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := -(2:ℝ)) (b := 2)).exists_bound_of_continuousOn hcont.continuousOn
  have hlog2 : (1:ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogpos : ∀ t : ℝ, Real.log 2 ≤ Real.log (2 + |t|) := fun t =>
    Real.log_le_log two_pos (by linarith [abs_nonneg t])
  refine ⟨max (2 * |M₀|) 16, by positivity, fun t => ?_⟩
  have hL2 : 0 < Real.log (2 + |t|) := lt_of_lt_of_le (by linarith) (hlogpos t)
  rcases le_or_gt |t| 2 with h | h
  · have := hM₀ t (abs_le.mp h)
    calc ‖L2 (((c:ℝ):ℂ) + t * I)‖ ≤ |M₀| := this.trans (le_abs_self _)
      _ ≤ (2 * |M₀|) * Real.log 2 := by nlinarith [abs_nonneg M₀]
      _ ≤ max (2 * |M₀|) 16 * Real.log (2 + |t|) :=
          mul_le_mul (le_max_left _ _) (hlogpos t) (by positivity) (by positivity)
  · -- |t| ≥ 2: ‖L₂‖ ≤ ‖L₂⋆‖ + 12/|t| ≤ log|t|/2 + 1 + 6
    have ht2 : 2 ≤ |t| := h.le
    have key : ‖L2 (((c:ℝ):ℂ) + t * I)‖ ≤ Real.log |t| / 2 + 7 := by
      have hmain : ∀ u : ℝ, 2 ≤ u → ‖L2 (((c:ℝ):ℂ) + u * I)‖ ≤ Real.log u / 2 + 7 := by
        intro u hu
        have hu0 : 0 < u := by linarith
        have h1 := norm_L2_sub_L2star_self_le' hc1 hc2 hu
        have h12 : 12 / u ≤ 6 := by rw [div_le_iff₀ hu0]; linarith
        have hstar : ‖((L2star u : ℝ) : ℂ)‖ ≤ Real.log u / 2 + 1 := by
          rw [Complex.norm_real, Real.norm_eq_abs]
          unfold L2star
          rw [Real.log_div hu0.ne' (by positivity), abs_le]
          have hlu : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
          have h2π : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
          constructor <;> nlinarith [log_two_pi_le_two]
        have := norm_le_norm_add_norm_sub' (L2 (((c:ℝ):ℂ) + u * I)) ((L2star u : ℝ) : ℂ)
        have h3 : ‖L2 (((c:ℝ):ℂ) + u * I)‖ ≤ ‖((L2star u : ℝ) : ℂ)‖ + ‖L2 (((c:ℝ):ℂ) + u * I) - ((L2star u : ℝ) : ℂ)‖ :=
          norm_le_insert' _ _
        linarith
      rcases le_or_gt 0 t with hpos | hneg
      · rw [abs_of_nonneg hpos] at ht2 ⊢; exact hmain t ht2
      · have ht' : 2 ≤ -t := by rwa [abs_of_neg hneg] at ht2
        have him : (((c:ℝ):ℂ) + (-t:ℝ) * I).im ≠ 0 := by rw [im_line]; linarith
        have e : ((c:ℝ):ℂ) + t * I = conj (((c:ℝ):ℂ) + (-t:ℝ) * I) := by rw [conj_line]; simp
        rw [e, L2_conj him, Complex.norm_conj, abs_of_neg hneg]
        exact hmain (-t) ht'
    have hlogle : Real.log |t| ≤ Real.log (2 + |t|) := Real.log_le_log (by linarith) (by linarith)
    calc ‖L2 (((c:ℝ):ℂ) + t * I)‖ ≤ Real.log |t| / 2 + 7 := key
      _ ≤ 16 * Real.log (2 + |t|) := by nlinarith [hlogpos t]
      _ ≤ max (2 * |M₀|) 16 * Real.log (2 + |t|) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hL2.le


/-- **ArchLineData for W** on 9/8 ≤ c ≤ 5/4: Λ = L₂, Λ⋆(τ) = (L2star τ : ℂ); fields from X1–X4 above. -/
theorem archLineData_L2 (hc1 : 9/8 ≤ c) (hc2 : c ≤ 5/4) :
    ArchLineData c L2 (fun τ => ((L2star τ : ℝ) : ℂ)) where
  one_lt := by linarith
  le := by linarith
  analytic := fun t => L2_analyticAt_goodStrip (mem_goodStrip_line hc1 hc2 t)
  conj_symm := fun z _ hz => L2_conj hz
  two_pt := norm_L2_sub_L2star_le hc1 hc2
  deriv_le := by
    obtain ⟨C, h⟩ := norm_deriv_L2_le hc1 hc2
    refine ⟨C, fun t ht => ?_⟩
    have h' := h t (by rw [abs_of_pos (by linarith)]; exact ht)
    rwa [abs_of_pos (by linarith : (0:ℝ) < t)] at h'
  lower := by
    obtain ⟨C, h⟩ := norm_L2_ge hc1 hc2
    refine ⟨C, fun t ht => ?_⟩
    have h' := h t (by rw [abs_of_pos (by linarith)]; exact ht)
    rwa [abs_of_pos (by linarith : (0:ℝ) < t)] at h'
  lower_par := ⟨1, fun τ hτ => norm_L2star_ge (by linarith)⟩
  upper := (norm_L2_line hc1 hc2).imp fun _ h => h.2

/-! ## X5–X6. The freeze on the line -/

section freeze

/-- E₂′/E₂ in the (L₂′+B)/(L₂−A) form on the line. -/
theorem derivE2_div_E2_eq_line (hc1 : 9/8 ≤ c) (hc2 : c ≤ 5/4) (t : ℝ) :
    deriv E2fn (((c:ℝ):ℂ) + t * I) / E2fn (((c:ℝ):ℂ) + t * I)
      = (deriv L2 (((c:ℝ):ℂ) + t * I) + Bfn (((c:ℝ):ℂ) + t * I))
          / (L2 (((c:ℝ):ℂ) + t * I) - Afn (((c:ℝ):ℂ) + t * I)) := by
  rw [deriv_E2fn (mem_goodStrip_line hc1 hc2 t), E2fn_eq_L2_sub_Afn (one_lt_re_line hc1 t)]

/-- **X5. the freezing estimate on the line Re s = c** [XF′ Lemma 2.4 for W]. -/
theorem freeze_on_line_W (hc1 : 9/8 ≤ c) (hc2 : c ≤ 5/4) :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ τ t : ℝ, T ≤ τ → T / 4 ≤ t →
      ‖deriv E2fn (((c:ℝ):ℂ) + t * I) / E2fn (((c:ℝ):ℂ) + t * I)
          - Bfn (((c:ℝ):ℂ) + t * I) / (((L2star τ : ℝ) : ℂ) - Afn (((c:ℝ):ℂ) + t * I))‖
        ≤ C * (|t - τ| + 1) / (T * Real.log T) :=
  (archLineData_L2 hc1 hc2).freeze_on_line

/-- **X6.** the frozen object is uniformly small on the line: ‖B/(L₂⋆(τ) − A(c+it))‖ ≤ 4B₀/log T. -/
theorem frozen_uniform_W (hc1 : 9/8 ≤ c) :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ τ t : ℝ, T ≤ τ →
      ‖Bfn (((c:ℝ):ℂ) + t * I) / (((L2star τ : ℝ) : ℂ) - Afn (((c:ℝ):ℂ) + t * I))‖ ≤ C / Real.log T := by
  obtain ⟨A₀, hA0, hA⟩ := norm_Afn_le_line hc1
  obtain ⟨B₀, hB0, hB⟩ := norm_Bfn_le_line hc1
  refine ⟨4 * B₀, max 8 (Real.exp (4 * (A₀ + 6))), by positivity, le_max_left _ _, ?_⟩
  intro T hT τ t hτ
  have hT8 : 8 ≤ T := le_trans (le_max_left _ _) hT
  have hT0 : 0 < T := by linarith
  have hτ0 : 0 < τ := by linarith
  have hlogT : 4 * (A₀ + 6) ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos _) (le_trans (le_max_right _ _) hT)
    rwa [Real.log_exp] at this
  have hlogτ : Real.log T ≤ Real.log τ := Real.log_le_log hT0 hτ
  have hΛ : Real.log T / 4 ≤ ‖((L2star τ : ℝ) : ℂ)‖ - A₀ := by
    have := norm_L2star_ge hτ0; nlinarith
  have hlogT1 : 1 ≤ Real.log T := by nlinarith
  have hq : 0 < Real.log T / 4 := by linarith
  have hden : Real.log T / 4 ≤ ‖((L2star τ : ℝ) : ℂ) - Afn (((c:ℝ):ℂ) + t * I)‖ :=
    hΛ.trans (norm_sub_ge_of_le (hA t))
  rw [norm_div]
  calc ‖Bfn (((c:ℝ):ℂ) + ↑t * I)‖ / ‖((L2star τ : ℝ) : ℂ) - Afn (((c:ℝ):ℂ) + ↑t * I)‖
      ≤ B₀ / (Real.log T / 4) := div_le_div₀ hB0 (hB t) hq hden
    _ = 4 * B₀ / Real.log T := by field_simp

end freeze

/-! ## X7. The uniform bound for E₂′/E₂ on the line (given W ≠ 0 there), continuity, conjugation -/

section uniform

theorem continuous_E2fn_line (hc1 : 9/8 ≤ c) (hc2 : c ≤ 5/4) :
    Continuous (fun t : ℝ => E2fn (((c:ℝ):ℂ) + t * I)) :=
  (archLineData_L2 hc1 hc2).continuous_E_line

theorem continuous_derivE2_line (hc1 : 9/8 ≤ c) (hc2 : c ≤ 5/4) :
    Continuous (fun t : ℝ => deriv E2fn (((c:ℝ):ℂ) + t * I)) :=
  (archLineData_L2 hc1 hc2).continuous_derivE_line

/-- continuity of t ↦ E₂′/E₂(c+it), given W ≠ 0 on the line. -/
theorem continuous_derivE2_div_E2_line (hc1 : 9/8 ≤ c) (hc2 : c ≤ 5/4)
    (hW : ∀ t : ℝ, hardyW (((c:ℝ):ℂ) + t * I) ≠ 0) :
    Continuous (fun t : ℝ => deriv E2fn (((c:ℝ):ℂ) + t * I) / E2fn (((c:ℝ):ℂ) + t * I)) :=
  (continuous_derivE2_line hc1 hc2).div (continuous_E2fn_line hc1 hc2)
    fun t => E2fn_ne_zero (one_lt_re_line hc1 t) (hW t)

/-- conjugation: E₂′/E₂(s̄) = conj(E₂′/E₂(s)) for s on the line with Im s ≠ 0 and W(s) ≠ 0. -/
theorem derivE2_div_E2_conj (hc1 : 9/8 ≤ c) (hc2 : c ≤ 5/4) {t : ℝ} (ht : t ≠ 0)
    (hW : hardyW (((c:ℝ):ℂ) + t * I) ≠ 0) :
    deriv E2fn (conj (((c:ℝ):ℂ) + t * I)) / E2fn (conj (((c:ℝ):ℂ) + t * I))
      = conj (deriv E2fn (((c:ℝ):ℂ) + t * I) / E2fn (((c:ℝ):ℂ) + t * I)) := by
  set s : ℂ := ((c:ℝ):ℂ) + t * I with hs
  have hsim : s.im ≠ 0 := by rw [hs, im_line]; exact ht
  have hsG : s ∈ GoodStrip := mem_goodStrip_line hc1 hc2 t
  have hcG : conj s ∈ GoodStrip := by
    rw [hs, conj_line]; exact mem_goodStrip_line hc1 hc2 (-t)
  have hWc : hardyW (conj s) ≠ 0 := by rw [hardyW_conj hsim]; simpa using hW
  rw [derivE2_div_E2_eq hcG hWc, derivE2_div_E2_eq hsG hW, FZfn_conj hsim, E2fn_conj hsim, map_sub]

/-- **X7. uniform bound**: given W ≠ 0 on Re s = c, ‖E₂′/E₂(c+it)‖ ≤ C_E for every real t. -/
theorem derivE2_div_E2_uniform (hc1 : 9/8 ≤ c) (hc2 : c ≤ 5/4)
    (hW : ∀ t : ℝ, hardyW (((c:ℝ):ℂ) + t * I) ≠ 0) :
    ∃ CE : ℝ, 0 ≤ CE ∧ ∀ t : ℝ,
      ‖deriv E2fn (((c:ℝ):ℂ) + t * I) / E2fn (((c:ℝ):ℂ) + t * I)‖ ≤ CE :=
  (archLineData_L2 hc1 hc2).derivE_div_E_uniform fun t => E2fn_ne_zero (one_lt_re_line hc1 t) (hW t)

/-- The conjugation symmetry in the `dE2` spelling: conj (E₂′/E₂(c − it)) = E₂′/E₂(c + it). -/
theorem derivE2_div_E2_conj_symm (hc1 : 9/8 ≤ c) (hc2 : c ≤ 5/4)
    (_hW : ∀ t : ℝ, hardyW (((c:ℝ):ℂ) + t * I) ≠ 0) (t : ℝ) (ht : t ≠ 0) :
    conj (deriv E2fn (((c:ℝ):ℂ) + ((-t : ℝ) : ℂ) * I) / E2fn (((c:ℝ):ℂ) + ((-t : ℝ) : ℂ) * I))
      = deriv E2fn (((c:ℝ):ℂ) + t * I) / E2fn (((c:ℝ):ℂ) + t * I) := by
  have h : deriv E2fn (((c:ℝ):ℂ) + ((-t : ℝ) : ℂ) * I) / E2fn (((c:ℝ):ℂ) + ((-t : ℝ) : ℂ) * I)
      = conj (deriv E2fn (((c:ℝ):ℂ) + t * I) / E2fn (((c:ℝ):ℂ) + t * I)) :=
    (archLineData_L2 hc1 hc2).derivE_div_E_conj ht
  rw [h, Complex.conj_conj]

end uniform

/-! ## X8. The line bounds and continuity for E₂ and F_𝒵 = L₂ + W′/W -/

section linebounds

/-- **X8a.** ‖E₂(c+it)‖ ≤ M log(2+|t|) and t ↦ E₂(c+it) is continuous. -/
theorem norm_E2fn_line (hc1 : 9/8 ≤ c) (hc2 : c ≤ 5/4) :
    ∃ M : ℝ, ∀ t : ℝ, ‖E2fn (((c:ℝ):ℂ) + t * I)‖ ≤ M * Real.log (2 + |t|) :=
  (archLineData_L2 hc1 hc2).norm_E_line

/-- **X8b. the line bound for F_𝒵 = L₂ + W′/W** (given W ≠ 0 on the line). -/
theorem norm_FZ_line (hc1 : 9/8 ≤ c) (hc2 : c ≤ 5/4) (hW : ∀ t : ℝ, hardyW (((c:ℝ):ℂ) + t * I) ≠ 0) :
    ∃ M : ℝ, ∀ t : ℝ, ‖L2 (((c:ℝ):ℂ) + t * I) + logDeriv hardyW (((c:ℝ):ℂ) + t * I)‖ ≤ M * Real.log (2 + |t|) := by
  obtain ⟨M, hM⟩ := norm_E2fn_line hc1 hc2
  obtain ⟨CE, hCE0, hCE⟩ := derivE2_div_E2_uniform hc1 hc2 hW
  have hlog2 : (1:ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogpos : ∀ t : ℝ, Real.log 2 ≤ Real.log (2 + |t|) := fun t =>
    Real.log_le_log two_pos (by linarith [abs_nonneg t])
  refine ⟨M + 2 * CE, fun t => ?_⟩
  have h := FZfn_eq (mem_goodStrip_line hc1 hc2 t) (hW t)
  unfold FZfn at h
  rw [h]
  calc ‖E2fn (((c:ℝ):ℂ) + t * I) + deriv E2fn (((c:ℝ):ℂ) + t * I) / E2fn (((c:ℝ):ℂ) + t * I)‖
      ≤ ‖E2fn (((c:ℝ):ℂ) + t * I)‖ + ‖deriv E2fn (((c:ℝ):ℂ) + t * I) / E2fn (((c:ℝ):ℂ) + t * I)‖ :=
        norm_add_le _ _
    _ ≤ M * Real.log (2 + |t|) + CE := add_le_add (hM t) (hCE t)
    _ ≤ (M + 2 * CE) * Real.log (2 + |t|) := by nlinarith [hlogpos t]

theorem continuous_FZ_line (hc1 : 9/8 ≤ c) (hc2 : c ≤ 5/4) (hW : ∀ t : ℝ, hardyW (((c:ℝ):ℂ) + t * I) ≠ 0) :
    Continuous (fun t : ℝ => L2 (((c:ℝ):ℂ) + t * I) + logDeriv hardyW (((c:ℝ):ℂ) + t * I)) := by
  have e : (fun t : ℝ => L2 (((c:ℝ):ℂ) + t * I) + logDeriv hardyW (((c:ℝ):ℂ) + t * I))
      = fun t : ℝ => E2fn (((c:ℝ):ℂ) + t * I)
          + deriv E2fn (((c:ℝ):ℂ) + t * I) / E2fn (((c:ℝ):ℂ) + t * I) := by
    funext t
    have h := FZfn_eq (mem_goodStrip_line hc1 hc2 t) (hW t)
    unfold FZfn at h
    exact h
  rw [e]
  exact (continuous_E2fn_line hc1 hc2).add (continuous_derivE2_div_E2_line hc1 hc2 hW)

end linebounds

/-! ## Packaged in the field order of `E2LineFacts` / `FreezeFactsW` -/

theorem e2LineFacts' (hc1 : 9/8 ≤ c) (hc2 : c ≤ 5/4) (hW : ∀ t : ℝ, hardyW (((c:ℝ):ℂ) + t * I) ≠ 0) :
    (∀ t : ℝ, hardyW (((c:ℝ):ℂ) + t * I) ≠ 0) ∧
    (∃ CE : ℝ, 0 ≤ CE ∧ ∀ t : ℝ, ‖deriv E2fn (((c:ℝ):ℂ) + t * I) / E2fn (((c:ℝ):ℂ) + t * I)‖ ≤ CE) ∧
    Continuous (fun t : ℝ => deriv E2fn (((c:ℝ):ℂ) + t * I) / E2fn (((c:ℝ):ℂ) + t * I)) :=
  ⟨hW, derivE2_div_E2_uniform hc1 hc2 hW, continuous_derivE2_div_E2_line hc1 hc2 hW⟩

theorem freezeFactsW' (hc1 : 9/8 ≤ c) (hc2 : c ≤ 5/4) (hW : ∀ t : ℝ, hardyW (((c:ℝ):ℂ) + t * I) ≠ 0) :
    (∃ C T₀ : ℝ, 0 ≤ C ∧ 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ τ t : ℝ, T ≤ τ → T / 4 ≤ t →
      ‖deriv E2fn (((c:ℝ):ℂ) + t * I) / E2fn (((c:ℝ):ℂ) + t * I)
          - Bfn (((c:ℝ):ℂ) + t * I) / (((L2star τ : ℝ) : ℂ) - Afn (((c:ℝ):ℂ) + t * I))‖
        ≤ C * (|t - τ| + 1) / (T * Real.log T)) ∧
    (∃ C T₀ : ℝ, 0 ≤ C ∧ 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ τ t : ℝ, T ≤ τ →
      ‖Bfn (((c:ℝ):ℂ) + t * I) / (((L2star τ : ℝ) : ℂ) - Afn (((c:ℝ):ℂ) + t * I))‖ ≤ C / Real.log T) ∧
    (∀ t : ℝ, t ≠ 0 → conj (deriv E2fn (((c:ℝ):ℂ) + ((-t : ℝ) : ℂ) * I) / E2fn (((c:ℝ):ℂ) + ((-t : ℝ) : ℂ) * I))
      = deriv E2fn (((c:ℝ):ℂ) + t * I) / E2fn (((c:ℝ):ℂ) + t * I)) :=
  ⟨freeze_on_line_W hc1 hc2, frozen_uniform_W hc1, derivE2_div_E2_conj_symm hc1 hc2 hW⟩

end Hardy
end XiPrime
end Zeta23

end
