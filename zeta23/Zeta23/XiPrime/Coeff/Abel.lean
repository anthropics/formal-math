/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Coeff/Abel.lean — the Mertens/Abel step.

[XF′ Lemma 7.1, proof, input (M)]: from Mertens' first theorem |Σ_{n≤t} Λ(n)/n − log t| ≤ K (K = log 4 + 4,
tree: Cheb.mertensFirst) and Abel summation, for g ∈ C¹[1,x]:
    | Σ_{n≤x} (Λ(n)/n)·g(n) − ∫₁ˣ g(t)/t dt |  ≤  K·( |g(x)| + ∫₁ˣ |g′(t)| dt ),                 (abel_mertens_t)
and, substituting t = eᵘ, for f ∈ C¹[0,y]:
    | Σ_{n≤e^y} (Λ(n)/n)·f(log n) − ∫₀ʸ f(u) du |  ≤  K·( |f(y)| + ∫₀ʸ |f′(u)| du ).             (mertens_step)
Every Mertens-level estimate for the coefficients (the recursion for the k-fold prime sums, the
Chebyshev-type upper bounds, the k = 1 terms) is an instance of mertens_step with a polynomial f.
-/
import Zeta23.Chebyshev
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

open scoped BigOperators ArithmeticFunction
open Finset Real MeasureTheory Set

noncomputable section

namespace Zeta23
namespace XiPrime

/-- Mertens' constant K := log 4 + 4. -/
def KM : ℝ := Real.log 4 + 4

lemma KM_pos : 0 < KM := by unfold KM; positivity
lemma KM_nonneg : 0 ≤ KM := KM_pos.le

/-- M(t) := Σ_{n≤t} Λ(n)/n in the Icc form produced by Mathlib's Abel summation (the n = 0 term is 0). -/
def Mfun (t : ℝ) : ℝ := ∑ n ∈ Icc 0 ⌊t⌋₊, Λ n / n

lemma sum_Icc_eq_sum_Ioc' {c : ℕ → ℝ} (hc : c 0 = 0) (n : ℕ) :
    ∑ k ∈ Icc 0 n, c k = ∑ k ∈ Ioc 0 n, c k := by
  rw [Icc_eq_cons_Ioc (Nat.zero_le n), sum_cons, hc, zero_add]

lemma Mfun_eq_Ioc (t : ℝ) : Mfun t = ∑ n ∈ Ioc 0 ⌊t⌋₊, Λ n / n :=
  sum_Icc_eq_sum_Ioc' (by simp) _

lemma Mfun_mono : Monotone Mfun := fun _ _ hab =>
  sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl (Nat.floor_le_floor hab))
    fun n _ _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)

lemma Mfun_nonneg (t : ℝ) : 0 ≤ Mfun t :=
  sum_nonneg fun n _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)

lemma abs_Mfun_sub_log_le {t : ℝ} (ht : 1 ≤ t) : |Mfun t - Real.log t| ≤ KM := by
  rw [Mfun_eq_Ioc]; exact Cheb.mertensFirst ht

/-- **Abel/Mertens, t-variable.**  For g ∈ C¹[1,x] (derivative g′, given pointwise as HasDerivAt and continuous):
  |Σ_{n≤x} (Λ(n)/n) g(n) − ∫₁ˣ g(t)/t dt| ≤ K (|g(x)| + ∫₁ˣ |g′(t)| dt). -/
theorem abel_mertens_t {x : ℝ} (hx : 1 ≤ x) {g g' : ℝ → ℝ}
    (hg : ∀ t ∈ Icc 1 x, HasDerivAt g (g' t) t) (hg' : ContinuousOn g' (Icc 1 x)) :
    |(∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n * g n) - ∫ t in (1:ℝ)..x, g t / t|
      ≤ KM * (|g x| + ∫ t in (1:ℝ)..x, |g' t|) := by
  have huIcc : uIcc 1 x = Icc 1 x := uIcc_of_le hx
  have hgc : ContinuousOn g (Icc 1 x) := fun t ht => (hg t ht).continuousAt.continuousWithinAt
  have hg'c : ContinuousOn g' (uIcc 1 x) := by rwa [huIcc]
  have hpos : ∀ t ∈ Icc (1:ℝ) x, 0 < t := fun t ht => lt_of_lt_of_le one_pos ht.1
  have hinvc : ContinuousOn (fun t : ℝ => t⁻¹) (Icc 1 x) :=
    continuousOn_inv₀.mono fun t ht => (hpos t ht).ne'
  have hlogc : ContinuousOn Real.log (Icc 1 x) := fun t ht =>
    (Real.continuousAt_log (hpos t ht).ne').continuousWithinAt
  -- (1) Abel summation
  have habel : ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n * g n
      = g x * Mfun x - ∫ t in (1:ℝ)..x, g' t * Mfun t := by
    have hdiff : ∀ t ∈ Icc 1 x, DifferentiableAt ℝ g t := fun t ht => (hg t ht).differentiableAt
    have hint : IntegrableOn (deriv g) (Icc 1 x) :=
      (hg'.integrableOn_Icc).congr_fun (fun t ht => ((hg t ht).deriv).symm) measurableSet_Icc
    have h := sum_mul_eq_sub_integral_mul₀ (fun n => Λ n / n) (by simp) x hdiff hint
    rw [sum_Icc_eq_sum_Ioc' (by simp)] at h
    have hL : ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n * g n = ∑ k ∈ Ioc 0 ⌊x⌋₊, g k * (Λ k / k) :=
      sum_congr rfl fun k _ => by ring
    rw [hL, h, intervalIntegral.integral_of_le hx]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [(hg t (Ioc_subset_Icc_self ht)).deriv]
    rfl
  -- (2) integration by parts for ∫ g/t:  (g·log)′ = g′ log + g/t
  have hparts : ∫ t in (1:ℝ)..x, g t / t = g x * Real.log x - ∫ t in (1:ℝ)..x, g' t * Real.log t := by
    have hderiv : ∀ t ∈ uIcc 1 x, HasDerivAt (fun t => g t * Real.log t) (g' t * Real.log t + g t / t) t := by
      intro t ht
      rw [huIcc] at ht
      have h1 := (hg t ht).mul (Real.hasDerivAt_log (hpos t ht).ne')
      simpa [div_eq_mul_inv, Pi.mul_def] using h1
    have hint1 : IntervalIntegrable (fun t => g' t * Real.log t) volume 1 x := by
      apply ContinuousOn.intervalIntegrable; rw [huIcc]; exact hg'.mul hlogc
    have hint2 : IntervalIntegrable (fun t => g t / t) volume 1 x := by
      apply ContinuousOn.intervalIntegrable; rw [huIcc]
      simpa [div_eq_mul_inv, Pi.mul_def] using hgc.mul hinvc
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hint1.add hint2)
    rw [intervalIntegral.integral_add hint1 hint2] at hftc
    simp only [Real.log_one, mul_zero, sub_zero] at hftc
    linarith
  -- (3) integrability facts for the error integral
  have hMint : IntervalIntegrable Mfun volume 1 x := Mfun_mono.intervalIntegrable
  have hEint : IntervalIntegrable (fun t => g' t * (Mfun t - Real.log t)) volume 1 x := by
    have h1 : IntervalIntegrable (fun t => g' t * Mfun t) volume 1 x := hMint.continuousOn_mul hg'c
    have h2 : IntervalIntegrable (fun t => g' t * Real.log t) volume 1 x := by
      apply ContinuousOn.intervalIntegrable; rw [huIcc]; exact hg'.mul hlogc
    have : (fun t => g' t * (Mfun t - Real.log t)) = (fun t => g' t * Mfun t) - fun t => g' t * Real.log t := by
      funext t; simp [mul_sub]
    rw [this]; exact h1.sub h2
  have habsint : IntervalIntegrable (fun t => |g' t|) volume 1 x := by
    apply ContinuousOn.intervalIntegrable; rw [huIcc]; exact hg'.abs
  -- (4) assemble
  have hkey : (∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / n * g n) - ∫ t in (1:ℝ)..x, g t / t
      = g x * (Mfun x - Real.log x) - ∫ t in (1:ℝ)..x, g' t * (Mfun t - Real.log t) := by
    rw [habel, hparts]
    have : ∫ t in (1:ℝ)..x, g' t * (Mfun t - Real.log t)
        = (∫ t in (1:ℝ)..x, g' t * Mfun t) - ∫ t in (1:ℝ)..x, g' t * Real.log t := by
      rw [← intervalIntegral.integral_sub (hMint.continuousOn_mul hg'c)]
      · exact intervalIntegral.integral_congr fun t _ => by ring
      · apply ContinuousOn.intervalIntegrable; rw [huIcc]; exact hg'.mul hlogc
    rw [this]; ring
  rw [hkey]
  have hb1 : |g x * (Mfun x - Real.log x)| ≤ KM * |g x| := by
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_Mfun_sub_log_le hx) (abs_nonneg _)
  have hb2 : |∫ t in (1:ℝ)..x, g' t * (Mfun t - Real.log t)| ≤ KM * ∫ t in (1:ℝ)..x, |g' t| := by
    calc |∫ t in (1:ℝ)..x, g' t * (Mfun t - Real.log t)|
        ≤ ∫ t in (1:ℝ)..x, |g' t * (Mfun t - Real.log t)| :=
          intervalIntegral.abs_integral_le_integral_abs hx
      _ ≤ ∫ t in (1:ℝ)..x, KM * |g' t| := by
          refine intervalIntegral.integral_mono_on hx hEint.abs (habsint.const_mul KM) fun t ht => ?_
          rw [abs_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right (abs_Mfun_sub_log_le ht.1) (abs_nonneg _)
      _ = KM * ∫ t in (1:ℝ)..x, |g' t| := intervalIntegral.integral_const_mul KM _
  calc |g x * (Mfun x - Real.log x) - ∫ t in (1:ℝ)..x, g' t * (Mfun t - Real.log t)|
      ≤ |g x * (Mfun x - Real.log x)| + |∫ t in (1:ℝ)..x, g' t * (Mfun t - Real.log t)| := abs_sub _ _
    _ ≤ KM * |g x| + KM * ∫ t in (1:ℝ)..x, |g' t| := add_le_add hb1 hb2
    _ = KM * (|g x| + ∫ t in (1:ℝ)..x, |g' t|) := by ring

/-- **Mertens step, u-variable.**  For f ∈ C¹[0,y] (y ≥ 0):
  |Σ_{n ≤ e^y} (Λ(n)/n) f(log n) − ∫₀ʸ f| ≤ K (|f(y)| + ∫₀ʸ |f′|). -/
theorem mertens_step {y : ℝ} (hy : 0 ≤ y) {f f' : ℝ → ℝ}
    (hf : ∀ u ∈ Icc 0 y, HasDerivAt f (f' u) u) (hf' : ContinuousOn f' (Icc 0 y)) :
    |(∑ n ∈ Ioc 0 ⌊Real.exp y⌋₊, Λ n / n * f (Real.log n)) - ∫ u in (0:ℝ)..y, f u|
      ≤ KM * (|f y| + ∫ u in (0:ℝ)..y, |f' u|) := by
  set x : ℝ := Real.exp y with hxdef
  have hx : 1 ≤ x := by rw [hxdef]; exact Real.one_le_exp hy
  have huIcc : uIcc 1 x = Icc 1 x := uIcc_of_le hx
  have hpos : ∀ t ∈ Icc (1:ℝ) x, 0 < t := fun t ht => lt_of_lt_of_le one_pos ht.1
  have hmaps : ∀ t ∈ Icc (1:ℝ) x, Real.log t ∈ Icc 0 y := fun t ht =>
    ⟨Real.log_nonneg ht.1, (Real.log_le_iff_le_exp (hpos t ht)).mpr ht.2⟩
  have himg : Real.log '' (uIcc 1 x) ⊆ Icc 0 y := by
    rw [huIcc]; rintro _ ⟨t, ht, rfl⟩; exact hmaps t ht
  have hfc : ContinuousOn f (Icc 0 y) := fun u hu => (hf u hu).continuousAt.continuousWithinAt
  have hlog' : ∀ t ∈ uIcc (1:ℝ) x, HasDerivAt Real.log t⁻¹ t := fun t ht =>
    Real.hasDerivAt_log (hpos t (huIcc ▸ ht)).ne'
  have hinvc : ContinuousOn (fun t : ℝ => t⁻¹) (uIcc 1 x) := by
    rw [huIcc]; exact continuousOn_inv₀.mono fun t ht => (hpos t ht).ne'
  -- g := f ∘ log
  have hg : ∀ t ∈ Icc 1 x, HasDerivAt (fun t => f (Real.log t)) (f' (Real.log t) * t⁻¹) t :=
    fun t ht => (hf _ (hmaps t ht)).comp t (Real.hasDerivAt_log (hpos t ht).ne')
  have hg' : ContinuousOn (fun t => f' (Real.log t) * t⁻¹) (Icc 1 x) := by
    refine ContinuousOn.mul ?_ (huIcc ▸ hinvc)
    exact hf'.comp (fun t ht => (Real.continuousAt_log (hpos t ht).ne').continuousWithinAt) hmaps
  have hmain := abel_mertens_t hx hg hg'
  -- substitute t = e^u in the two integrals
  have hsub1 : ∫ t in (1:ℝ)..x, f (Real.log t) / t = ∫ u in (0:ℝ)..y, f u := by
    have h := intervalIntegral.integral_comp_mul_deriv' hlog' hinvc (hfc.mono himg)
    simp only [Function.comp, Real.log_one, hxdef, Real.log_exp] at h
    rw [← hxdef] at h
    simpa [div_eq_mul_inv] using h
  have hsub2 : ∫ t in (1:ℝ)..x, |f' (Real.log t) * t⁻¹| = ∫ u in (0:ℝ)..y, |f' u| := by
    have h := intervalIntegral.integral_comp_mul_deriv' hlog' hinvc ((hf'.abs).mono himg)
    simp only [Function.comp, Real.log_one, hxdef, Real.log_exp] at h
    rw [← hxdef] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun t ht => ?_
    have ht' : 0 < t := hpos t (huIcc ▸ ht)
    simp only [abs_mul, abs_inv, abs_of_pos ht']
  have hfy : f (Real.log x) = f y := by rw [hxdef, Real.log_exp]
  rw [hsub1, hsub2, hfy] at hmain
  exact hmain

end XiPrime
end Zeta23
