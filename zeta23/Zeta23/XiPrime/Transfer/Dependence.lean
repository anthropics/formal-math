/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization.

Zeta23/XiPrime/Transfer/Dependence.lean — ξ′ TRACE TRANSFER: [XF′ Lemma 6.1] AT FIXED T over the
abstract taper data (p : PrimeSide.Setting, F : PrimeSide.LocalFun, LocalHypsCore).

  A. integrability / linearity of the prime-side entry in the coefficients:
     GentryW 1 c₁ − GentryW 1 c₂ = GentryNu (P_{c₁−c₂})  (the μ and Π_X parts cancel);
     Q_{kl}(e) := GentryNu (P_e) k l is a FINITE ℝ-linear functional of (Re e_N, Im e_N)_{N≤X}, so an
     entrywise expansion e^{kl}_N = Σ_r e_r(N) δ_{kl}^r (HasSum) transfers to Q_{kl}(e^{kl}) = Σ_r δ^r Q_{kl}(e_r).
  B. the Dirichlet-kernel bound A_φ(y)‖Σ_{k<K} e^{−iτ_k y}‖ ≤ L²/(2 log 2) for EVERY K (ThmE's
     Aphi_mul_norm_tauKernel_le is the case K = d), and Abel summation in k with complex summands.
  C. the two fixed-T conclusions: Frobenius (Minkowski over r, Abstract §B) and trace (Abel over k).
-/
import Zeta23.XiPrime.Transfer.Inputs
import Zeta23.XiPrime.Transfer.Abstract
import Zeta23.XiPrime.PrimeSide.Trace

noncomputable section

open Finset Filter Topology RHLinalg MeasureTheory Real
open scoped BigOperators

namespace Zeta23
namespace XiPrime
namespace Transfer

open PrimeSide

variable {cϱ : ℝ} {p : Setting} {Fn : LocalFun}

/-! ### A. Integrability, linearity, and Q as a finite linear functional -/

lemma Pc_sub (X : ℝ) (c₁ c₂ : ℕ → ℂ) (τ : ℝ) : Pc X c₁ τ - Pc X c₂ τ = Pc X (c₁ - c₂) τ := by
  unfold Pc
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun N _ => ?_
  simp only [Pi.sub_apply, Complex.sub_re, Complex.sub_im]
  ring

/-- φ̂(·−τ_k) φ̂(·−τ_l) g is integrable for g continuous and bounded (2|ab| ≤ a² + b²). -/
lemma integrable_phiHat_mul_mul_bdd (hF : LocalHypsCore cϱ p Fn) (k l : ℤ) {g : ℝ → ℝ}
    (hg : Continuous g) {c : ℝ} (hc : ∀ x, |g x| ≤ c) :
    Integrable (fun τ => Fn.phiHat (τ - p.tau k) * Fn.phiHat (τ - p.tau l) * g τ) := by
  have hc0 : 0 ≤ c := (abs_nonneg _).trans (hc 0)
  have h1 : Integrable (fun τ => Fn.phiHat (τ - p.tau k) ^ 2) :=
    hF.phiHat_sq_integrable.comp_sub_right (p.tau k)
  have h2 : Integrable (fun τ => Fn.phiHat (τ - p.tau l) ^ 2) :=
    hF.phiHat_sq_integrable.comp_sub_right (p.tau l)
  refine Integrable.mono' ((h1.add h2).mul_const (c / 2)) ?_ ?_
  · have := hF.phiHat_cont
    exact (by fun_prop : Continuous fun τ =>
      Fn.phiHat (τ - p.tau k) * Fn.phiHat (τ - p.tau l) * g τ).aestronglyMeasurable
  · refine Eventually.of_forall fun τ => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    set a := Fn.phiHat (τ - p.tau k)
    set b := Fn.phiHat (τ - p.tau l)
    have hab : |a| * |b| ≤ (a ^ 2 + b ^ 2) / 2 := by
      nlinarith [sq_abs a, sq_abs b, sq_nonneg (|a| - |b|)]
    calc |a| * |b| * |g τ| ≤ (a ^ 2 + b ^ 2) / 2 * c :=
          mul_le_mul hab (hc τ) (abs_nonneg _) (by positivity)
      _ = (a ^ 2 + b ^ 2) * (c / 2) := by ring

/-- φ̂(·−t)² ν is integrable for ν = μ + ϖ·Π_X + P_c, t > 0 (translate the three diagonal part lemmas). -/
lemma integrable_phiHat_sq_shift_mul_nucW (hΓ : Zeta23.GammaFacts) (hF : LocalHypsCore cϱ p Fn)
    (cPi : ℝ) (c : ℕ → ℂ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun τ => Fn.phiHat (τ - t) ^ 2 * nucW cPi p.X c τ) := by
  have h := ((mu_part_integrable hΓ hF ht).add ((Pi_part_integrable hF t).const_mul cPi)).add
    (Pc_part_integrable hF c t)
  have h' := h.comp_sub_right t
  refine h'.congr (Eventually.of_forall fun τ => ?_)
  simp only [Pi.add_apply, nucW, add_sub_cancel]
  ring

/-- the full integrand of GentryW ϖ c is integrable (0 < τ_k, τ_l). -/
lemma integrable_gentryW_integrand (hΓ : Zeta23.GammaFacts) (hF : LocalHypsCore cϱ p Fn) (hX : 0 < p.X)
    (cPi : ℝ) (c : ℕ → ℂ) {k l : ℤ} (hk : 0 < p.tau k) (hl : 0 < p.tau l) :
    Integrable (fun τ => Fn.phiHat (τ - p.tau k) * Fn.phiHat (τ - p.tau l) * nucW cPi p.X c τ) := by
  have h1 := (integrable_phiHat_sq_shift_mul_nucW hΓ hF cPi c hk).norm
  have h2 := (integrable_phiHat_sq_shift_mul_nucW hΓ hF cPi c hl).norm
  refine Integrable.mono' ((h1.add h2).div_const 2) ?_ ?_
  · have := hF.phiHat_cont
    have := nucW_continuous hΓ hX cPi c
    exact (by fun_prop : Continuous fun τ =>
      Fn.phiHat (τ - p.tau k) * Fn.phiHat (τ - p.tau l) * nucW cPi p.X c τ).aestronglyMeasurable
  · refine Eventually.of_forall fun τ => ?_
    simp only [Real.norm_eq_abs, abs_mul, Pi.add_apply, abs_pow, sq_abs]
    set a := Fn.phiHat (τ - p.tau k)
    set b := Fn.phiHat (τ - p.tau l)
    set v := |nucW cPi p.X c τ|
    have hv : 0 ≤ v := abs_nonneg _
    have hab : |a| * |b| ≤ (a ^ 2 + b ^ 2) / 2 := by
      nlinarith [sq_abs a, sq_abs b, sq_nonneg (|a| - |b|)]
    calc |a| * |b| * v ≤ (a ^ 2 + b ^ 2) / 2 * v := mul_le_mul_of_nonneg_right hab hv
      _ = (a ^ 2 * v + b ^ 2 * v) / 2 := by ring

/-- **linearity**: the μ- and Π-parts cancel in a difference of two fixed-coefficient entries (any pole weight). -/
lemma gentryW_sub (hΓ : Zeta23.GammaFacts) (hF : LocalHypsCore cϱ p Fn) (hX : 0 < p.X) (cPi : ℝ)
    (c₁ c₂ : ℕ → ℂ) {k l : ℤ} (hk : 0 < p.tau k) (hl : 0 < p.tau l) :
    GentryW cPi c₁ p Fn k l - GentryW cPi c₂ p Fn k l = GentryNu (Pc p.X (c₁ - c₂)) p Fn k l := by
  simp only [GentryW, GentryNu]
  rw [← integral_sub (integrable_gentryW_integrand hΓ hF hX cPi c₁ hk hl)
    (integrable_gentryW_integrand hΓ hF hX cPi c₂ hk hl)]
  congr 1
  funext τ
  rw [← Pc_sub]
  simp only [nucW]
  ring

lemma gentryW_one_sub (hΓ : Zeta23.GammaFacts) (hF : LocalHypsCore cϱ p Fn) (hX : 0 < p.X)
    (c₁ c₂ : ℕ → ℂ) {k l : ℤ} (hk : 0 < p.tau k) (hl : 0 < p.tau l) :
    GentryW 1 c₁ p Fn k l - GentryW 1 c₂ p Fn k l = GentryNu (Pc p.X (c₁ - c₂)) p Fn k l :=
  gentryW_sub hΓ hF hX 1 c₁ c₂ hk hl

/-- **the pole-weight difference**: GentryW ϖ₁ c − GentryW ϖ₂ c = (ϖ₁ − ϖ₂)·(Π-part entry). -/
lemma gentryW_weight_sub (hΓ : Zeta23.GammaFacts) (hF : LocalHypsCore cϱ p Fn) (hX : 0 < p.X)
    (cPi₁ cPi₂ : ℝ) (c : ℕ → ℂ) {k l : ℤ} (hk : 0 < p.tau k) (hl : 0 < p.tau l) :
    GentryW cPi₁ c p Fn k l - GentryW cPi₂ c p Fn k l
      = (cPi₁ - cPi₂) * GentryNu (Zeta23.PiX p.X) p Fn k l := by
  simp only [GentryW, GentryNu]
  rw [← integral_sub (integrable_gentryW_integrand hΓ hF hX cPi₁ c hk hl)
    (integrable_gentryW_integrand hΓ hF hX cPi₂ c hk hl), ← integral_const_mul]
  congr 1
  funext τ
  simp only [nucW]
  ring

section Qsum
variable (p Fn)

/-- the cosine weight of frequency log N in Q_{kl}:  ∫ φ̂_k φ̂_l cos(τ log N)/(π√N). -/
def Jc (k l : ℤ) (N : ℕ) : ℝ :=
  ∫ τ, Fn.phiHat (τ - p.tau k) * Fn.phiHat (τ - p.tau l)
    * (Real.cos (τ * Real.log N) / (Real.pi * Real.sqrt N))

/-- the sine weight. -/
def Js (k l : ℤ) (N : ℕ) : ℝ :=
  ∫ τ, Fn.phiHat (τ - p.tau k) * Fn.phiHat (τ - p.tau l)
    * (Real.sin (τ * Real.log N) / (Real.pi * Real.sqrt N))

end Qsum

lemma abs_trig_div_le (x N : ℝ) (f : ℝ → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    |f x / (Real.pi * Real.sqrt N)| ≤ 1 / (Real.pi * Real.sqrt N) := by
  rw [abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.pi * Real.sqrt N)]
  exact div_le_div_of_nonneg_right (hf x) (by positivity)

/-- **Q_{kl}(e) as a finite ℝ-linear functional of the coefficients**:
GentryNu (P_e) k l = Σ_{N≤X} (Re e_N · Jc N + Im e_N · Js N). -/
lemma gentryNu_Pc_eq_sum (hF : LocalHypsCore cϱ p Fn) (e : ℕ → ℂ) (k l : ℤ) :
    GentryNu (Pc p.X e) p Fn k l
      = ∑ N ∈ Finset.Ioc 0 ⌊p.X⌋₊, ((e N).re * Jc p Fn k l N + (e N).im * Js p Fn k l N) := by
  unfold GentryNu
  have h1 : (fun τ => Fn.phiHat (τ - p.tau k) * Fn.phiHat (τ - p.tau l) * Pc p.X e τ)
      = fun τ => ∑ N ∈ Finset.Ioc 0 ⌊p.X⌋₊,
          ((e N).re * (Fn.phiHat (τ - p.tau k) * Fn.phiHat (τ - p.tau l)
              * (Real.cos (τ * Real.log N) / (Real.pi * Real.sqrt N)))
            + (e N).im * (Fn.phiHat (τ - p.tau k) * Fn.phiHat (τ - p.tau l)
              * (Real.sin (τ * Real.log N) / (Real.pi * Real.sqrt N)))) := by
    funext τ
    unfold Pc
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun N _ => ?_
    field_simp
  rw [h1, integral_finset_sum]
  · refine Finset.sum_congr rfl fun N _ => ?_
    have ic : Integrable (fun τ => Fn.phiHat (τ - p.tau k) * Fn.phiHat (τ - p.tau l)
        * (Real.cos (τ * Real.log N) / (Real.pi * Real.sqrt N))) :=
      integrable_phiHat_mul_mul_bdd hF k l (g := fun τ =>
        Real.cos (τ * Real.log N) / (Real.pi * Real.sqrt N)) (by fun_prop)
        (fun x => abs_trig_div_le _ _ (fun u => Real.cos (u * Real.log N))
          (fun u => Real.abs_cos_le_one _))
    have is : Integrable (fun τ => Fn.phiHat (τ - p.tau k) * Fn.phiHat (τ - p.tau l)
        * (Real.sin (τ * Real.log N) / (Real.pi * Real.sqrt N))) :=
      integrable_phiHat_mul_mul_bdd hF k l (g := fun τ =>
        Real.sin (τ * Real.log N) / (Real.pi * Real.sqrt N)) (by fun_prop)
        (fun x => abs_trig_div_le _ _ (fun u => Real.sin (u * Real.log N))
          (fun u => Real.abs_sin_le_one _))
    rw [integral_add (ic.const_mul _) (is.const_mul _), integral_const_mul, integral_const_mul]
    rfl
  · intro N _
    have ic := integrable_phiHat_mul_mul_bdd hF k l (g := fun τ =>
        Real.cos (τ * Real.log N) / (Real.pi * Real.sqrt N)) (by fun_prop)
        (fun x => abs_trig_div_le _ _ (fun u => Real.cos (u * Real.log N))
          (fun u => Real.abs_cos_le_one _))
    have is := integrable_phiHat_mul_mul_bdd hF k l (g := fun τ =>
        Real.sin (τ * Real.log N) / (Real.pi * Real.sqrt N)) (by fun_prop)
        (fun x => abs_trig_div_le _ _ (fun u => Real.sin (u * Real.log N))
          (fun u => Real.abs_sin_le_one _))
    exact (ic.const_mul _).add (is.const_mul _)

/-- **series transfer**: an entrywise expansion of the coefficients transfers to Q_{kl}. -/
theorem hasSum_gentryNu_Pc (hF : LocalHypsCore cϱ p Fn) {g : ℕ → ℂ} {e : ℕ → ℕ → ℂ} {δ : ℝ}
    (k l : ℤ)
    (h : ∀ N ∈ Finset.Ioc 0 ⌊p.X⌋₊, HasSum (fun r : ℕ => e (r + 1) N * (δ : ℂ) ^ (r + 1)) (g N)) :
    HasSum (fun r : ℕ => δ ^ (r + 1) * GentryNu (Pc p.X (e (r + 1))) p Fn k l)
      (GentryNu (Pc p.X g) p Fn k l) := by
  rw [gentryNu_Pc_eq_sum hF]
  have hN : ∀ N ∈ Finset.Ioc 0 ⌊p.X⌋₊, HasSum
      (fun r : ℕ => (e (r + 1) N * (δ : ℂ) ^ (r + 1)).re * Jc p Fn k l N
        + (e (r + 1) N * (δ : ℂ) ^ (r + 1)).im * Js p Fn k l N)
      ((g N).re * Jc p Fn k l N + (g N).im * Js p Fn k l N) := by
    intro N hN
    have hre := (Complex.reCLM.hasSum (h N hN)).mul_right (Jc p Fn k l N)
    have him := (Complex.imCLM.hasSum (h N hN)).mul_right (Js p Fn k l N)
    simp only [Complex.reCLM_apply, Complex.imCLM_apply] at hre him
    exact hre.add him
  have := hasSum_sum hN
  convert this using 1
  funext r
  rw [gentryNu_Pc_eq_sum hF, Finset.mul_sum]
  refine Finset.sum_congr rfl fun N _ => ?_
  rw [← Complex.ofReal_pow, Complex.re_mul_ofReal, Complex.im_mul_ofReal]
  ring

/-! ### B. The Dirichlet kernel for every K, and Abel summation with complex summands -/

/-- A_φ(y)·‖Σ_{k<K} e^{−iτ_k y}‖ ≤ L²/(2 log 2) for every K (proof = ThmE.Aphi_mul_norm_tauKernel_le with
p.d ↦ K; that lemma's geometric-sum input abs_sin_mul_norm_geom_le is already K-general). -/
lemma Aphi_mul_norm_tauKernel_le' (hF : LocalHypsCoreW cϱ p Fn) {y : ℝ} (hy : Real.log 2 ≤ y)
    (K : ℕ) :
    Fn.Aphi y * ‖∑ k ∈ Finset.range K, Complex.exp ((-(p.tau k * y) : ℝ) * Complex.I)‖
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
  · have hz : Fn.Aphi y = 0 := le_antisymm ((hF.Aphi_le y).trans (by simp [hyabs, hyL])) hA0
    simp [hz, hRHS]
  · set m := min y (p.L - y) with hm
    have hy0 : 0 < y := hlog2.trans_le hy
    have hm0 : 0 < m := lt_min hy0 (by linarith)
    have hfac : ∑ k ∈ Finset.range K, Complex.exp ((-(p.tau k * y) : ℝ) * Complex.I)
        = Complex.exp ((-(p.T * y) : ℝ) * Complex.I)
          * ∑ k ∈ Finset.range K, Complex.exp (((k : ℝ) * (-(p.h * y)) : ℝ) * Complex.I) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Complex.exp_add]
      congr 1
      simp only [Setting.tau]
      push_cast
      ring
    have hnorm : ‖∑ k ∈ Finset.range K, Complex.exp ((-(p.tau k * y) : ℝ) * Complex.I)‖
        = ‖∑ k ∈ Finset.range K, Complex.exp (((k : ℝ) * (-(p.h * y)) : ℝ) * Complex.I)‖ := by
      rw [hfac, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    have hdir := ThmE.abs_sin_mul_norm_geom_le (-(p.h * y)) K
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
    set S := ‖∑ k ∈ Finset.range K, Complex.exp (((k : ℝ) * (-(p.h * y)) : ℝ) * Complex.I)‖
      with hS
    have hS0 : 0 ≤ S := norm_nonneg _
    rw [hsin_eq] at hdir
    have hS1 : 2 * m / p.L * S ≤ 1 :=
      (mul_le_mul_of_nonneg_right hsin hS0).trans hdir
    have hS2 : 2 * m * S ≤ p.L := by
      have h4 := mul_le_mul_of_nonneg_left hS1 hL.le
      rw [mul_one, ← mul_assoc, mul_div_cancel₀ _ hL.ne'] at h4
      linarith
    have hA1 : Fn.Aphi y ≤ p.L - y := (hF.Aphi_le y).trans (by simp [hyabs, hyL.le])
    have key : (p.L - y) * Real.log 2 ≤ p.L * m := by
      rcases le_total y (p.L - y) with h | h
      · rw [hm, min_eq_left h]
        nlinarith
      · rw [hm, min_eq_right h]
        nlinarith
    rw [le_div_iff₀ (by positivity)]
    calc Fn.Aphi y * S * (2 * Real.log 2) = (Fn.Aphi y * Real.log 2) * (2 * S) := by ring
      _ ≤ ((p.L - y) * Real.log 2) * (2 * S) := by gcongr
      _ ≤ (p.L * m) * (2 * S) := by gcongr
      _ = p.L * (2 * m * S) := by ring
      _ ≤ p.L * p.L := by gcongr
      _ = p.L ^ 2 := (sq _).symm

/-- Abel summation with monotone bounded real weights and vector summands:
‖Σ_{k<d} w_k • q_k‖ ≤ 2WB when every ‖Σ_{k<K} q_k‖ ≤ B (K ≤ d). -/
theorem norm_sum_smul_le_of_monotone {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (d : ℕ) (w : ℕ → ℝ) (q : ℕ → E) {W B : ℝ}
    (hw0 : ∀ k, 0 ≤ w k) (hwW : ∀ k, w k ≤ W) (hmono : Monotone w)
    (hq : ∀ K ≤ d, ‖∑ k ∈ Finset.range K, q k‖ ≤ B) :
    ‖∑ k ∈ Finset.range d, w k • q k‖ ≤ 2 * W * B := by
  have hB0 : 0 ≤ B := by simpa using hq 0 (Nat.zero_le _)
  have hW0 : 0 ≤ W := (hw0 0).trans (hwW 0)
  rw [Finset.sum_range_by_parts w q d]
  have h1 : ‖w (d - 1) • ∑ k ∈ Finset.range d, q k‖ ≤ W * B := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw0 _)]
    exact mul_le_mul (hwW _) (hq d le_rfl) (norm_nonneg _) hW0
  have h2 : ‖∑ i ∈ Finset.range (d - 1), (w (i + 1) - w i) • ∑ k ∈ Finset.range (i + 1), q k‖
      ≤ W * B := by
    refine (norm_sum_le _ _).trans ?_
    have h3 : ∀ i ∈ Finset.range (d - 1),
        ‖(w (i + 1) - w i) • ∑ k ∈ Finset.range (i + 1), q k‖ ≤ (w (i + 1) - w i) * B := by
      intro i hi
      have hi' : i + 1 ≤ d := by
        have := Finset.mem_range.1 hi; omega
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 (hmono (Nat.le_succ i)))]
      exact mul_le_mul_of_nonneg_left (hq _ hi') (sub_nonneg.2 (hmono (Nat.le_succ i)))
    refine (Finset.sum_le_sum h3).trans ?_
    rw [← Finset.sum_mul, Finset.sum_range_sub]
    have : w (d - 1) - w 0 ≤ W := by linarith [hw0 0, hwW (d - 1)]
    exact mul_le_mul_of_nonneg_right this hB0
  calc ‖w (d - 1) • ∑ k ∈ Finset.range d, q k
        - ∑ i ∈ Finset.range (d - 1), (w (i + 1) - w i) • ∑ k ∈ Finset.range (i + 1), q k‖
      ≤ ‖w (d - 1) • ∑ k ∈ Finset.range d, q k‖
        + ‖∑ i ∈ Finset.range (d - 1), (w (i + 1) - w i) • ∑ k ∈ Finset.range (i + 1), q k‖ :=
          norm_sub_le _ _
    _ ≤ W * B + W * B := add_le_add h1 h2
    _ = 2 * W * B := by ring

/-- the per-frequency oscillating sum of [XF′ Lemma 6.1]'s trace part, with monotone weights
0 ≤ w_k ≤ W:  |Σ_{k<d} w_k A_φ(y)(a cos(τ_k y) + b sin(τ_k y))| ≤ ‖a + bi‖ · 2W · L²/(2 log 2)
for y ≥ log 2  (a cos + b sin = Re((a+bi)e^{−iτy})). -/
theorem abs_weighted_diag_sum_le (hF : LocalHypsCoreW cϱ p Fn) {y : ℝ} (hy : Real.log 2 ≤ y)
    (d : ℕ) (w : ℕ → ℝ) {W : ℝ} (hw0 : ∀ k, 0 ≤ w k) (hwW : ∀ k, w k ≤ W) (hmono : Monotone w)
    (z : ℂ) :
    |∑ k ∈ Finset.range d, w k * (Fn.Aphi y *
        (z.re * Real.cos (p.tau k * y) + z.im * Real.sin (p.tau k * y)))|
      ≤ ‖z‖ * (2 * W * (p.L ^ 2 / (2 * Real.log 2))) := by
  -- the kernel vectors q_k := A(y) e^{-i τ_k y}
  set q : ℕ → ℂ := fun k => (Fn.Aphi y : ℂ) * Complex.exp ((-(p.tau k * y) : ℝ) * Complex.I)
    with hq
  have hqK : ∀ K ≤ d, ‖∑ k ∈ Finset.range K, q k‖ ≤ p.L ^ 2 / (2 * Real.log 2) := by
    intro K _
    rw [hq, ← Finset.mul_sum, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hF.Aphi_nonneg y)]
    exact Aphi_mul_norm_tauKernel_le' hF hy K
  have habel := norm_sum_smul_le_of_monotone d w q hw0 hwW hmono hqK
  -- identify the real sum with Re(z * Σ w_k • q_k)
  have hre : ∑ k ∈ Finset.range d, w k * (Fn.Aphi y *
      (z.re * Real.cos (p.tau k * y) + z.im * Real.sin (p.tau k * y)))
      = (z * ∑ k ∈ Finset.range d, w k • q k).re := by
    rw [Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hq]
    simp only [Complex.real_smul]
    rw [Complex.exp_mul_I]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.add_re, Complex.add_im, Complex.cos_ofReal_re, Complex.cos_ofReal_im,
      Complex.sin_ofReal_re, Complex.sin_ofReal_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg, Complex.neg_re, Complex.neg_im]
    ring
  rw [hre]
  calc |(z * ∑ k ∈ Finset.range d, w k • q k).re|
      ≤ ‖z * ∑ k ∈ Finset.range d, w k • q k‖ := Complex.abs_re_le_norm _
    _ = ‖z‖ * ‖∑ k ∈ Finset.range d, w k • q k‖ := norm_mul _ _
    _ ≤ ‖z‖ * (2 * W * (p.L ^ 2 / (2 * Real.log 2))) :=
        mul_le_mul_of_nonneg_left habel (norm_nonneg _)

/-! ### C. The fixed-T conclusions -/

/-- geometric partial sums: Σ_{r<R} x^{r+1} ≤ 2x for 0 ≤ x ≤ 1/2. -/
lemma geom_partial_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (R : ℕ) :
    ∑ r ∈ Finset.range R, x ^ (r + 1) ≤ 2 * x := by
  have hx1 : x < 1 := by linarith
  have hs : Summable (fun r : ℕ => x ^ (r + 1)) := by
    simp_rw [pow_succ]
    exact (summable_geometric_of_lt_one hx0 hx1).mul_right x
  calc ∑ r ∈ Finset.range R, x ^ (r + 1) ≤ ∑' r : ℕ, x ^ (r + 1) :=
        hs.sum_le_tsum _ (fun r _ => by positivity)
    _ = x * ∑' r : ℕ, x ^ r := by
        rw [← tsum_mul_left]; congr 1; funext r; ring
    _ = x * (1 - x)⁻¹ := by rw [tsum_geometric_of_lt_one hx0 hx1]
    _ ≤ x * 2 := by
        gcongr
        rw [inv_le_comm₀ (by linarith) two_pos]; linarith
    _ = 2 * x := mul_comm _ _


lemma hasSum_geom_succ {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun r : ℕ => x ^ (r + 1)) (x * (1 - x)⁻¹) := by
  have := (hasSum_geometric_of_lt_one hx0 hx1).mul_left x
  simpa [pow_succ'] using this

lemma mul_inv_one_sub_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) : x * (1 - x)⁻¹ ≤ 2 * x := by
  rw [mul_comm]
  gcongr
  rw [inv_le_comm₀ (by linarith) two_pos]; linarith

/-- cast helper: frobSq of a real d×d matrix indexed through Fin d → ℕ, as a double range sum. -/
lemma frobSq_ofReal_fin (d : ℕ) (M : ℕ → ℕ → ℝ) :
    frobSq (fun (k l : Fin d) => ((M k l : ℝ) : ℂ)) = ∑ k ∈ Finset.range d, ∑ l ∈ Finset.range d, M k l ^ 2 := by
  erw [Assembly.frobSq_eq_sum_norm_sq]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  calc ∑ k : Fin d, ∑ l : Fin d, M k l ^ 2 = ∑ k : Fin d, ∑ l ∈ Finset.range d, M k l ^ 2 :=
        Finset.sum_congr rfl fun k _ => Fin.sum_univ_eq_sum_range (fun l => M k l ^ 2) d
    _ = ∑ k ∈ Finset.range d, ∑ l ∈ Finset.range d, M k l ^ 2 :=
        Fin.sum_univ_eq_sum_range (fun k => ∑ l ∈ Finset.range d, M k l ^ 2) d

/-- **[XF′ Lemma 6.1], Frobenius part, at fixed T.**  If every entry's coefficient sequence expands as
g^{kl}_N = Σ_{r≥1} e_r(N) δ_{kl}^r with 0 ≤ δ_{kl} ≤ 1/2, and Σ_{kl} Q_{kl}(e_r)² ≤ K₁ρ^{2r} + K₀ (ρ ≤ 1),
then Σ_{kl} Q_{kl}(g^{kl})² ≤ 2(K₁ρ² + K₀). -/
theorem dependence_frob (hF : LocalHypsCore cϱ p Fn) {e : ℕ → ℕ → ℂ} {g : ℕ → ℕ → ℕ → ℂ}
    {δm : ℕ → ℕ → ℝ} (hδ0 : ∀ k l, 0 ≤ δm k l) (hδ1 : ∀ k l, δm k l ≤ 1 / 2)
    (hexp : ∀ k, k < p.d → ∀ l, l < p.d → ∀ N ∈ Finset.Ioc 0 ⌊p.X⌋₊,
      HasSum (fun r : ℕ => e (r + 1) N * (δm k l : ℂ) ^ (r + 1)) (g k l N))
    {K₁ K₀ ρ : ℝ} (hK₁ : 0 ≤ K₁) (hK₀ : 0 ≤ K₀) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hQ : ∀ r : ℕ, 1 ≤ r → (∑ k ∈ Finset.range p.d, ∑ l ∈ Finset.range p.d,
      GentryNu (Pc p.X (e r)) p Fn k l ^ 2) ≤ K₁ * ρ ^ (2 * r) + K₀) :
    (∑ k ∈ Finset.range p.d, ∑ l ∈ Finset.range p.d, GentryNu (Pc p.X (g k l)) p Fn k l ^ 2)
      ≤ 2 * (K₁ * ρ ^ 2 + K₀) := by
  set d := p.d with hd
  set D : Matrix (Fin d) (Fin d) ℂ :=
    fun k l => ((GentryNu (Pc p.X (g k l)) p Fn k l : ℝ) : ℂ) with hD
  set Q : ℕ → Matrix (Fin d) (Fin d) ℂ :=
    fun r k l => ((GentryNu (Pc p.X (e r)) p Fn k l : ℝ) : ℂ) with hQdef
  set S : ℕ → Matrix (Fin d) (Fin d) ℂ :=
    fun r k l => ((δm k l ^ (r + 1) : ℝ) : ℂ) * Q (r + 1) k l with hSdef
  set s : ℕ → ℝ := fun r => (1 / 2) ^ (r + 1) * (Real.sqrt K₁ * ρ ^ (r + 1) + Real.sqrt K₀) with hs
  have hfrobQ : ∀ r, 1 ≤ r → frobSq (Q r) ≤ K₁ * ρ ^ (2 * r) + K₀ := by
    intro r hr
    have e1 : frobSq (Q r) = ∑ k ∈ Finset.range d, ∑ l ∈ Finset.range d,
        GentryNu (Pc p.X (e r)) p Fn k l ^ 2 :=
      frobSq_ofReal_fin d (fun k l => GentryNu (Pc p.X (e r)) p Fn k l)
    rw [e1]; exact hQ r hr
  have hs0 : ∀ r, 0 ≤ s r := fun r => by positivity
  have hS : ∀ r, frobSq (S r) ≤ s r ^ 2 := by
    intro r
    have h1 : frobSq (S r) ≤ ((1 / 2 : ℝ) ^ (r + 1)) ^ 2 * frobSq (Q (r + 1)) := by
      refine frobSq_hadamard_le (fun (k l : Fin d) => δm k l ^ (r + 1)) (Q (r + 1)) (fun k l => ?_)
      rw [abs_of_nonneg (pow_nonneg (hδ0 _ _) _)]
      exact pow_le_pow_left₀ (hδ0 _ _) (hδ1 _ _) _
    have h2 := hfrobQ (r + 1) (by omega)
    have h3 : K₁ * ρ ^ (2 * (r + 1)) + K₀ ≤ (Real.sqrt K₁ * ρ ^ (r + 1) + Real.sqrt K₀) ^ 2 := by
      have e1 : (Real.sqrt K₁ * ρ ^ (r + 1)) ^ 2 = K₁ * ρ ^ (2 * (r + 1)) := by
        rw [mul_pow, Real.sq_sqrt hK₁, ← pow_mul, mul_comm (r + 1) 2]
      have e2 : Real.sqrt K₀ ^ 2 = K₀ := Real.sq_sqrt hK₀
      nlinarith [mul_nonneg (mul_nonneg (Real.sqrt_nonneg K₁) (pow_nonneg hρ0 (r + 1)))
        (Real.sqrt_nonneg K₀)]
    calc frobSq (S r) ≤ ((1 / 2 : ℝ) ^ (r + 1)) ^ 2 * frobSq (Q (r + 1)) := h1
      _ ≤ ((1 / 2 : ℝ) ^ (r + 1)) ^ 2 * (K₁ * ρ ^ (2 * (r + 1)) + K₀) := by gcongr
      _ ≤ ((1 / 2 : ℝ) ^ (r + 1)) ^ 2 * (Real.sqrt K₁ * ρ ^ (r + 1) + Real.sqrt K₀) ^ 2 := by gcongr
      _ = s r ^ 2 := by rw [hs]; ring
  have hB : ∀ R, ∑ r ∈ Finset.range R, s r ≤ Real.sqrt K₁ * ρ + Real.sqrt K₀ := by
    intro R
    have hK : 0 ≤ Real.sqrt K₁ * ρ + Real.sqrt K₀ := by positivity
    have h1 : ∀ r, s r ≤ (Real.sqrt K₁ * ρ + Real.sqrt K₀) * (1 / 2 : ℝ) ^ (r + 1) := by
      intro r
      rw [hs]
      have : ρ ^ (r + 1) ≤ ρ := by
        calc ρ ^ (r + 1) = ρ * ρ ^ r := pow_succ' _ _
          _ ≤ ρ * 1 := by gcongr; exact pow_le_one₀ hρ0 hρ1
          _ = ρ := mul_one _
      have h0 : (0:ℝ) ≤ (1 / 2 : ℝ) ^ (r + 1) := by positivity
      have : Real.sqrt K₁ * ρ ^ (r + 1) + Real.sqrt K₀ ≤ Real.sqrt K₁ * ρ + Real.sqrt K₀ := by
        gcongr
      nlinarith
    calc ∑ r ∈ Finset.range R, s r
        ≤ ∑ r ∈ Finset.range R, (Real.sqrt K₁ * ρ + Real.sqrt K₀) * (1 / 2 : ℝ) ^ (r + 1) :=
          Finset.sum_le_sum fun r _ => h1 r
      _ = (Real.sqrt K₁ * ρ + Real.sqrt K₀) * ∑ r ∈ Finset.range R, (1 / 2 : ℝ) ^ (r + 1) := by
          rw [Finset.mul_sum]
      _ ≤ (Real.sqrt K₁ * ρ + Real.sqrt K₀) * (2 * (1 / 2)) := by
          gcongr; exact geom_partial_le (by norm_num) le_rfl R
      _ = Real.sqrt K₁ * ρ + Real.sqrt K₀ := by ring
  have hlim : ∀ i j : Fin d, Tendsto (fun R => ∑ r ∈ Finset.range R, S r i j) atTop (𝓝 (D i j)) := by
    intro i j
    have h := hasSum_gentryNu_Pc hF (i : ℤ) (j : ℤ) (hexp i i.isLt j j.isLt)
    have h2 := (Complex.ofRealCLM.hasSum h).tendsto_sum_nat
    simp only [Complex.ofRealCLM_apply, Complex.ofReal_mul] at h2
    convert h2 using 1
  have hfin := frobSq_le_of_tendsto_partialSums D S s hs0 hS hB hlim
  have eD : frobSq D = ∑ k ∈ Finset.range d, ∑ l ∈ Finset.range d,
      GentryNu (Pc p.X (g k l)) p Fn k l ^ 2 :=
    frobSq_ofReal_fin d (fun k l => GentryNu (Pc p.X (g k l)) p Fn k l)
  rw [eD] at hfin
  calc _ ≤ (Real.sqrt K₁ * ρ + Real.sqrt K₀) ^ 2 := hfin
    _ ≤ 2 * (K₁ * ρ ^ 2 + K₀) := by
        have e1 : (Real.sqrt K₁ * ρ) ^ 2 = K₁ * ρ ^ 2 := by rw [mul_pow, Real.sq_sqrt hK₁]
        have e2 : Real.sqrt K₀ ^ 2 = K₀ := Real.sq_sqrt hK₀
        nlinarith [sq_nonneg (Real.sqrt K₁ * ρ - Real.sqrt K₀)]

/-- translation: the diagonal entry as ∫ φ̂(s)² P_c(τ_k + s) ds. -/
lemma gentryNu_Pc_diag (c : ℕ → ℂ) (k : ℤ) :
    GentryNu (Pc p.X c) p Fn k k = ∫ s, Fn.phiHat s ^ 2 * Pc p.X c (p.tau k + s) := by
  unfold GentryNu
  rw [← integral_add_right_eq_self _ (p.tau k)]
  congr 1
  funext s
  rw [add_sub_cancel_right, add_comm s (p.tau k)]
  ring

/-- **[XF′ Lemma 6.1], trace part, at fixed T.**  With the diagonal expansion g^{k}_N = Σ_{r≥1} e_r(N) δ_k^r
(0 ≤ δ_k ≤ 1/2, δ_k monotone in k), e_r(1) = 0 and S₁(e_r) ≤ σρ^r (ρ ≤ 1):
|Σ_{k<d} Q_{kk}(g^k)| ≤ (2/log 2)·L²·σ·ρ  (Abel in k against the Dirichlet kernel). -/
theorem dependence_trace (hF : LocalHypsCore cϱ p Fn) {e : ℕ → ℕ → ℂ} (he1 : ∀ r, e r 1 = 0)
    {g : ℕ → ℕ → ℂ} {δv : ℕ → ℝ} (hδ0 : ∀ k, 0 ≤ δv k) (hδ1 : ∀ k, δv k ≤ 1 / 2)
    (hmono : Monotone δv)
    (hexp : ∀ k, k < p.d → ∀ N ∈ Finset.Ioc 0 ⌊p.X⌋₊,
      HasSum (fun r : ℕ => e (r + 1) N * (δv k : ℂ) ^ (r + 1)) (g k N))
    {σ ρ : ℝ} (hσ : 0 ≤ σ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hS1 : ∀ r : ℕ, 1 ≤ r → S1 (e r) p.X ≤ σ * ρ ^ r) :
    |∑ k ∈ Finset.range p.d, GentryNu (Pc p.X (g k)) p Fn k k|
      ≤ 2 / Real.log 2 * p.L ^ 2 * σ * ρ := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set Tm : ℕ → ℝ := fun r => ∑ k ∈ Finset.range p.d,
    δv k ^ (r + 1) * GentryNu (Pc p.X (e (r + 1))) p Fn k k with hTm
  have hT : HasSum Tm (∑ k ∈ Finset.range p.d, GentryNu (Pc p.X (g k)) p Fn k k) :=
    hasSum_sum fun k hk => hasSum_gentryNu_Pc hF k k (hexp k (Finset.mem_range.1 hk))
  set Kc : ℝ := 2 * p.L ^ 2 / Real.log 2 * σ with hKc
  have hKc0 : 0 ≤ Kc := by positivity
  set u : ℕ → ℝ := fun r => Kc * ((ρ / 2) ^ (r + 1)) with hu
  -- the bound on each |Tm r|
  have hTu : ∀ r, |Tm r| ≤ u r := by
    intro r
    set c := e (r + 1) with hc
    set w : ℕ → ℝ := fun k => δv k ^ (r + 1) with hw
    have hw0 : ∀ k, 0 ≤ w k := fun k => pow_nonneg (hδ0 k) _
    have hwW : ∀ k, w k ≤ (1 / 2 : ℝ) ^ (r + 1) := fun k => pow_le_pow_left₀ (hδ0 k) (hδ1 k) _
    have hwm : Monotone w := fun a b hab => pow_le_pow_left₀ (hδ0 a) (hmono hab) _
    -- rewrite Tm r with the diagonal formula and swap sums
    have eT : Tm r = 2 * ∑ N ∈ Finset.Ioc 0 ⌊p.X⌋₊, (Real.sqrt N)⁻¹ *
        ∑ k ∈ Finset.range p.d, w k * (Fn.Aphi (Real.log N) *
          ((c N).re * Real.cos (p.tau k * Real.log N) + (c N).im * Real.sin (p.tau k * Real.log N))) := by
      rw [hTm]
      simp only []
      have : ∀ k : ℕ, GentryNu (Pc p.X (e (r + 1))) p Fn k k
          = 2 * ∑ N ∈ Finset.Ioc 0 ⌊p.X⌋₊, (Real.sqrt N)⁻¹ * Fn.Aphi (Real.log N)
            * ((c N).re * Real.cos (p.tau k * Real.log N)
              + (c N).im * Real.sin (p.tau k * Real.log N)) := by
        intro k
        rw [gentryNu_Pc_diag, hc]
        exact Pc_part_eq hF.toCoreW _ _
      simp only [this, Finset.mul_sum]
      conv_lhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun N _ => Finset.sum_congr rfl fun k _ => ?_
      simp only [hw]
      ring
    -- bound per N
    have hN : ∀ N ∈ Finset.Ioc 0 ⌊p.X⌋₊,
        |∑ k ∈ Finset.range p.d, w k * (Fn.Aphi (Real.log N) *
          ((c N).re * Real.cos (p.tau k * Real.log N) + (c N).im * Real.sin (p.tau k * Real.log N)))|
          ≤ ‖c N‖ * (2 * (1 / 2 : ℝ) ^ (r + 1) * (p.L ^ 2 / (2 * Real.log 2))) := by
      intro N hNmem
      rcases Nat.lt_or_ge N 2 with hN2 | hN2
      · have hN1 : N = 1 := by have := (Finset.mem_Ioc.1 hNmem).1; omega
        subst hN1
        have : c 1 = 0 := by rw [hc]; exact he1 _
        simp [this]
      · exact abs_weighted_diag_sum_le hF.toCoreW
          (Real.log_le_log two_pos (by exact_mod_cast hN2)) p.d w hw0 hwW hwm (c N)
    rw [eT, abs_mul, abs_two]
    calc 2 * |∑ N ∈ Finset.Ioc 0 ⌊p.X⌋₊, (Real.sqrt N)⁻¹ *
          ∑ k ∈ Finset.range p.d, w k * (Fn.Aphi (Real.log N) *
            ((c N).re * Real.cos (p.tau k * Real.log N) + (c N).im * Real.sin (p.tau k * Real.log N)))|
        ≤ 2 * ∑ N ∈ Finset.Ioc 0 ⌊p.X⌋₊, (Real.sqrt N)⁻¹ *
            (‖c N‖ * (2 * (1 / 2 : ℝ) ^ (r + 1) * (p.L ^ 2 / (2 * Real.log 2)))) := by
          gcongr
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun N hNm => ?_)
          rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (Real.sqrt N)⁻¹)]
          exact mul_le_mul_of_nonneg_left (hN N hNm) (by positivity)
      _ = (2 * p.L ^ 2 / Real.log 2) * (1 / 2 : ℝ) ^ (r + 1) * S1 c p.X := by
          rw [S1, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun N _ => ?_
          rw [div_eq_mul_inv]
          ring
      _ ≤ (2 * p.L ^ 2 / Real.log 2) * (1 / 2 : ℝ) ^ (r + 1) * (σ * ρ ^ (r + 1)) := by
          gcongr; rw [hc]; exact hS1 (r + 1) (by omega)
      _ = u r := by
          show _ = Kc * (ρ / 2) ^ (r + 1)
          rw [hKc, show ρ / 2 = (1 / 2) * ρ by ring, mul_pow]; ring
  -- summing the geometric majorant
  have hρ2 : ρ / 2 ≤ 1 / 2 := by linarith
  have hρ20 : 0 ≤ ρ / 2 := by positivity
  have hu_has : HasSum u (Kc * ((ρ / 2) * (1 - ρ / 2)⁻¹)) :=
    (hasSum_geom_succ hρ20 (by linarith)).mul_left Kc
  have hu_sum : Summable u := hu_has.summable
  have hsT : Summable (fun r => ‖Tm r‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun r => by rw [Real.norm_eq_abs]; exact hTu r) hu_sum
  rw [← hT.tsum_eq]
  calc |∑' r, Tm r| = ‖∑' r, Tm r‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' r, ‖Tm r‖ := norm_tsum_le_tsum_norm hsT
    _ ≤ ∑' r, u r :=
        Summable.tsum_le_tsum (fun r => by rw [Real.norm_eq_abs]; exact hTu r) hsT hu_sum
    _ = Kc * ((ρ / 2) * (1 - ρ / 2)⁻¹) := hu_has.tsum_eq
    _ ≤ Kc * (2 * (ρ / 2)) := mul_le_mul_of_nonneg_left (mul_inv_one_sub_le hρ20 hρ2) hKc0
    _ = 2 / Real.log 2 * p.L ^ 2 * σ * ρ := by rw [hKc]; field_simp

end Transfer
end XiPrime
end Zeta23
