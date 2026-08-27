/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/ZeroCount/GenericRvM.lean — the GENERIC half-contour fold and Riemann–von Mangoldt main-term assembly.

Two facts abstracted over the function (instantiated both for ξ′ and for Ω = Γℝ·W):
 (A) `rectangleIntegral_eq_halfContour_of_fold`: if F(1 − s̄) = −conj F(s) along the right half of ∂([−1,2]×[T₁,T₂]) and F is
     continuous along the two horizontal lines, then ∮_{∂([−1,2]×[T₁,T₂])} F = 2i·Im(halfContour F T₁ T₂);
     `natCast_eq_im_halfContour`: so a count N with (1/2πi)∮F = N satisfies N = (1/π)·Im halfContour F.
 (B) `rvM_main_of`: for a ZeroConfig Zc, a good-height predicate with one good height per unit interval above a₀, the
     identity Zc.N T₁ T₂ = (1/π)Im halfContour(logDeriv Λ) at good heights, a residual bound
     |Im halfContour(logDeriv Λ) − Im halfContour(Γℝ′/Γℝ)| ≤ C log(|T₁|+3) + K + C log(|T₂|+3), and a local count, one gets
     |Zc.N(T,2T) − (T/2π)ℓ₁(T)| ≤ C′ log T — the μ-bookkeeping against Zeta23.RvM.gamma_side, done once.
Instances: Hardy/Contour.lean + Hardy/Count.lean (W); the ξ′ versions in ZeroCount.lean can be re-derived from these.
-/
import Zeta23.XiPrime.ZeroCount.Basic
import Zeta23.RvM.Defs
import Zeta23.RvM.GammaSide
import Zeta23.GammaFacts.Complete
import Zeta23.Analytic.RectangleLogDeriv

open Complex Set Filter Topology MeasureTheory intervalIntegral
open scoped ComplexConjugate

noncomputable section

namespace Zeta23
namespace XiPrime
namespace ZeroCount
namespace GenericRvM

open Zeta23.RvM (halfContour)

/-! ### (A) the fold -/

section fold

variable {F : ℂ → ℂ} {T₁ T₂ : ℝ}

/-- horizontal fold at height T: ∫_{−1}^{2} F(σ+iT)dσ = 2i·Im ∫_{1/2}^{2} F(σ+iT)dσ, given continuity along the line and
F(1 − s̄) = −conj F(s) at s = x + iT, x ∈ [1/2, 2]. -/
lemma horizontal_fold_of (T : ℝ) (hcont : Continuous fun σ : ℝ => F (σ + T * I))
    (hfold : ∀ x ∈ uIcc (1 / 2 : ℝ) 2, F (1 - conj ((x : ℂ) + T * I)) = -conj (F ((x : ℂ) + T * I))) :
    ∫ σ in (-1 : ℝ)..2, F (σ + T * I) = 2 * I * ((∫ σ in (1 / 2 : ℝ)..2, F (σ + T * I)).im : ℂ) := by
  have hsplit := integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) (-1) (1 / 2)) (hcont.intervalIntegrable (μ := volume) (1 / 2) 2)
  rw [← hsplit]
  set A := ∫ σ in (1 / 2 : ℝ)..2, F (σ + T * I) with hA
  have hleft : ∫ σ in (-1 : ℝ)..(1 / 2), F (σ + T * I) = -starRingEnd ℂ A := by
    have hsub := intervalIntegral.integral_comp_sub_left (f := fun x : ℝ => F (x + T * I)) (a := (1 / 2 : ℝ)) (b := 2) (1 : ℝ)
    norm_num at hsub
    rw [← hsub, hA, ← intervalIntegral_conj, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x hx
    have key := hfold x hx
    have e : (1 : ℂ) - starRingEnd ℂ ((x : ℂ) + T * I) = 1 - (x : ℂ) + T * I := by simp [Complex.ext_iff]
    simp only
    rw [← e, key]
  rw [hleft, neg_add_eq_sub, Complex.sub_conj]
  push_cast
  ring

/-- vertical fold: ∫_{T₁}^{T₂} F(−1+it)dt = −conj ∫_{T₁}^{T₂} F(2+it)dt. -/
lemma vertical_fold_of (hfold : ∀ t ∈ uIcc T₁ T₂, F (1 - conj ((2 : ℂ) + t * I)) = -conj (F ((2 : ℂ) + t * I))) :
    ∫ t in T₁..T₂, F (-1 + t * I) = -starRingEnd ℂ (∫ t in T₁..T₂, F (2 + t * I)) := by
  rw [← intervalIntegral_conj, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro t ht
  have e : (1 : ℂ) - starRingEnd ℂ (2 + t * I) = -1 + t * I := by simp [Complex.ext_iff]; norm_num
  show F (-1 + t * I) = -starRingEnd ℂ (F (2 + t * I))
  rw [← e, hfold t ht]

/-- **(A) the fold**: ∮_{∂([−1,2]×[T₁,T₂])} F = 2i·Im(halfContour F T₁ T₂). -/
theorem rectangleIntegral_eq_halfContour_of_fold
    (hc₁ : Continuous fun σ : ℝ => F (σ + T₁ * I)) (hc₂ : Continuous fun σ : ℝ => F (σ + T₂ * I))
    (hf₁ : ∀ x ∈ uIcc (1 / 2 : ℝ) 2, F (1 - conj ((x : ℂ) + T₁ * I)) = -conj (F ((x : ℂ) + T₁ * I)))
    (hf₂ : ∀ x ∈ uIcc (1 / 2 : ℝ) 2, F (1 - conj ((x : ℂ) + T₂ * I)) = -conj (F ((x : ℂ) + T₂ * I)))
    (hfv : ∀ t ∈ uIcc T₁ T₂, F (1 - conj ((2 : ℂ) + t * I)) = -conj (F ((2 : ℂ) + t * I))) :
    RectangleIntegral F (-1 + T₁ * I) (2 + T₂ * I) = 2 * I * ((halfContour F T₁ T₂).im : ℂ) := by
  have hre1 : (-1 + T₁ * I).re = -1 := by simp
  have him1 : (-1 + T₁ * I).im = T₁ := by simp
  have hre2 : (2 + T₂ * I : ℂ).re = 2 := by simp
  have him2 : (2 + T₂ * I : ℂ).im = T₂ := by simp
  simp only [RectangleIntegral, HIntegral, VIntegral, hre1, him1, hre2, him2, smul_eq_mul,
    Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [horizontal_fold_of T₁ hc₁ hf₁, horizontal_fold_of T₂ hc₂ hf₂, vertical_fold_of hfv]
  simp only [Zeta23.RvM.halfContour, Complex.add_im, Complex.sub_im, Complex.mul_I_im]
  generalize (∫ σ in (1 / 2 : ℝ)..2, F (σ + T₁ * I)) = A₁
  generalize (∫ σ in (1 / 2 : ℝ)..2, F (σ + T₂ * I)) = A₂
  generalize (∫ t in T₁..T₂, F (2 + t * I)) = B
  have e1 : 2 * I * (A₁.im : ℂ) - 2 * I * (A₂.im : ℂ) + I * B - I * -starRingEnd ℂ B
      = 2 * I * (A₁.im : ℂ) - 2 * I * (A₂.im : ℂ) + I * (B + starRingEnd ℂ B) := by ring
  rw [e1, Complex.add_conj]
  push_cast
  ring

/-- from (1/2πi)∮F = N and the fold: N = (1/π)·Im halfContour F. -/
theorem natCast_eq_im_halfContour {N : ℕ}
    (hN : RectangleIntegral' F (-1 + T₁ * I) (2 + T₂ * I) = (N : ℂ))
    (hfold : RectangleIntegral F (-1 + T₁ * I) (2 + T₂ * I) = 2 * I * ((halfContour F T₁ T₂).im : ℂ)) :
    (N : ℝ) = (1 / Real.pi) * (halfContour F T₁ T₂).im := by
  have h := hN
  change (1 / (2 * Real.pi * I)) • RectangleIntegral _ _ _ = _ at h
  rw [hfold, smul_eq_mul] at h
  have h' : ((N : ℝ) : ℂ) = (((1 / Real.pi) * (halfContour F T₁ T₂).im : ℝ) : ℂ) := by
    push_cast; rw [← h]; field_simp
  exact_mod_cast h'

end fold

/-! ### (B) the main-term assembly -/

set_option maxHeartbeats 1000000 in
/-- **(B) Riemann–von Mangoldt main term, generic**. -/
theorem rvM_main_of (Zc : ZeroConfig) (Good : ℝ → Prop) (Λ : ℂ → ℂ) {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hgood : ∀ a : ℝ, a₀ ≤ a → ∃ T ∈ Icc a (a + 1), Good T)
    (hcount : ∀ T₁ T₂ : ℝ, a₀ ≤ T₁ → T₁ ≤ T₂ → Good T₁ → Good T₂ →
      (Zc.N T₁ T₂ : ℝ) = (1 / Real.pi) * (halfContour (logDeriv Λ) T₁ T₂).im)
    (hres : ∃ C K T₀ : ℝ, 0 < C ∧ 0 ≤ K ∧ ∀ T₁ T₂ : ℝ, T₀ ≤ T₁ → T₁ ≤ T₂ → Good T₁ → Good T₂ →
      |(halfContour (logDeriv Λ) T₁ T₂).im - (halfContour (logDeriv Complex.Gammaℝ) T₁ T₂).im|
        ≤ C * Real.log (|T₁| + 3) + K + C * Real.log (|T₂| + 3))
    (hloc : ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ t : ℝ, (Zc.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → |(Zc.N T (2 * T) : ℝ) - T / (2 * Real.pi) * ell1 T| ≤ C * Real.log T := by
  obtain ⟨CY, KY, TY, hCY, hKY, hYb⟩ := hres
  obtain ⟨A₀, hA₀1, hA₀⟩ := hloc
  have hΓ : GammaFacts := Zeta23.gammaFacts
  obtain ⟨Cμ, Tμ, hCμ⟩ := hΓ.int_mu
  obtain ⟨CM, hCM0, hCM⟩ := Zeta23.RvM.mu_le_log hΓ
  have hμc : Continuous mu := Zeta23.RvM.mu_continuous hΓ
  have hA₀0 : 0 ≤ A₀ := by linarith
  refine ⟨4 * CY + KY + 1 + 4 * A₀ + 4 * CM + |Cμ|, max (max (max (TY + 1) (Tμ + 1)) 4) (a₀ + 1), fun T hT' => ?_⟩
  have hT : max (max (TY + 1) (Tμ + 1)) 4 ≤ T := le_trans (le_max_left _ _) hT'
  have hTa₀ : a₀ + 1 ≤ T := le_trans (le_max_right _ _) hT'
  have hT4 : 4 ≤ T := le_trans (le_max_right _ _) hT
  have hTY : TY + 1 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTμ : Tμ + 1 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hlogT : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (le_trans (by linarith [Real.exp_one_lt_d9]) le_rfl)
  have hlogT0 : 0 < Real.log T := by linarith
  obtain ⟨T₁, hT₁mem, hg1⟩ := hgood (T - 1) (by linarith)
  obtain ⟨T₂, hT₂mem, hg2⟩ := hgood (2 * T) (by linarith)
  have hT₁a : T - 1 ≤ T₁ := hT₁mem.1
  have hT₁b : T₁ ≤ T := by have := hT₁mem.2; linarith
  have hT₂a : 2 * T ≤ T₂ := hT₂mem.1
  have hT₂b : T₂ ≤ 2 * T + 1 := hT₂mem.2
  have h1T₁ : 1 ≤ T₁ := by linarith
  have h12 : T₁ ≤ T₂ := by linarith
  have hN := hcount T₁ T₂ (by linarith) h12 hg1 hg2
  have hgam := Zeta23.RvM.gamma_side (T₁ := T₁) (T₂ := T₂) (by linarith) (by linarith)
  have hYpart := hYb T₁ T₂ (by linarith) h12 hg1 hg2
  have hadd : (Zc.N T₁ T₂ : ℝ) = (Zc.N T₁ T : ℝ) + (Zc.N T (2 * T) : ℝ) + (Zc.N (2 * T) T₂ : ℝ) := by
    rw [Zc.N_add hT₁b (by linarith : T ≤ T₂), Zc.N_add (by linarith : T ≤ 2 * T) hT₂a]
    push_cast; ring
  have hlogsq : ∀ x : ℝ, 0 < x → x + 3 ≤ T ^ 2 → Real.log (x + 3) ≤ 2 * Real.log T := by
    intro x hx hxT
    calc Real.log (x + 3) ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith) hxT
      _ = 2 * Real.log T := by rw [Real.log_pow]; push_cast; ring
  have hw1 : (Zc.N T₁ T : ℝ) ≤ 2 * A₀ * Real.log T := by
    have hsub : Zc.N T₁ T ≤ Zc.N T₁ (T₁ + 1) := Zc.N_mono le_rfl (by linarith)
    calc (Zc.N T₁ T : ℝ) ≤ (Zc.N T₁ (T₁ + 1) : ℝ) := by exact_mod_cast hsub
      _ ≤ A₀ * Real.log (|T₁| + 3) := hA₀ T₁
      _ ≤ A₀ * (2 * Real.log T) := by
          refine mul_le_mul_of_nonneg_left ?_ hA₀0
          rw [abs_of_pos (by linarith : 0 < T₁)]
          exact hlogsq T₁ (by linarith) (by nlinarith)
      _ = 2 * A₀ * Real.log T := by ring
  have hw2 : (Zc.N (2 * T) T₂ : ℝ) ≤ 2 * A₀ * Real.log T := by
    have hsub : Zc.N (2 * T) T₂ ≤ Zc.N (2 * T) (2 * T + 1) := Zc.N_mono le_rfl hT₂b
    calc (Zc.N (2 * T) T₂ : ℝ) ≤ (Zc.N (2 * T) (2 * T + 1) : ℝ) := by exact_mod_cast hsub
      _ ≤ A₀ * Real.log (|2 * T| + 3) := hA₀ (2 * T)
      _ ≤ A₀ * (2 * Real.log T) := by
          refine mul_le_mul_of_nonneg_left ?_ hA₀0
          rw [abs_of_pos (by linarith : 0 < 2 * T)]
          exact hlogsq (2 * T) (by linarith) (by nlinarith)
      _ = 2 * A₀ * Real.log T := by ring
  -- the residual is O(log T)
  set Rres : ℝ := (halfContour (logDeriv Λ) T₁ T₂).im - (halfContour (logDeriv Complex.Gammaℝ) T₁ T₂).im with hRres
  have hYlog : |Rres| ≤ 4 * CY * Real.log T + KY := by
    have e1 : Real.log (|T₁| + 3) ≤ 2 * Real.log T := by
      rw [abs_of_pos (by linarith : 0 < T₁)]; exact hlogsq T₁ (by linarith) (by nlinarith)
    have e2 : Real.log (|T₂| + 3) ≤ 2 * Real.log T := by
      rw [abs_of_pos (by linarith : 0 < T₂)]; exact hlogsq T₂ (by linarith) (by nlinarith)
    have := mul_le_mul_of_nonneg_left e1 hCY.le
    have := mul_le_mul_of_nonneg_left e2 hCY.le
    linarith
  -- μ-integral bookkeeping
  have hμint : ∀ a b : ℝ, IntervalIntegrable mu volume a b := fun a b => hμc.intervalIntegrable a b
  have hμsplit : (∫ t in T₁..T₂, mu t)
      = (∫ t in T₁..T, mu t) + (∫ t in T..(2 * T), mu t) + ∫ t in (2 * T)..T₂, mu t := by
    have e1 : (∫ t in T₁..(2 * T), mu t) = (∫ t in T₁..T, mu t) + ∫ t in T..(2 * T), mu t :=
      (integral_add_adjacent_intervals (hμint T₁ T) (hμint T (2 * T))).symm
    have e2 : (∫ t in T₁..T₂, mu t) = (∫ t in T₁..(2 * T), mu t) + ∫ t in (2 * T)..T₂, mu t :=
      (integral_add_adjacent_intervals (hμint T₁ (2 * T)) (hμint (2 * T) T₂)).symm
    rw [e2, e1]
  have hμwin : ∀ a b : ℝ, 1 ≤ a → a ≤ b → b ≤ 2 * T + 1 → |b - a| ≤ 1 →
      |∫ t in a..b, mu t| ≤ 2 * CM * Real.log T := by
    intro a b ha hab hb hba
    have hbound : ∀ t ∈ Set.uIoc a b, ‖mu t‖ ≤ CM * Real.log (2 * T + 4) := by
      intro t ht
      rw [Set.uIoc_of_le hab] at ht
      have ht1 : 1 ≤ t := le_trans ha ht.1.le
      have ht2 : t ≤ 2 * T + 1 := le_trans ht.2 hb
      rw [Real.norm_eq_abs]
      refine (hCM t ht1).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hCM0.le
      exact Real.log_le_log (by linarith) (by linarith)
    have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [Real.norm_eq_abs] at this
    have hlog24 : Real.log (2 * T + 4) ≤ 2 * Real.log T := by
      calc Real.log (2 * T + 4) ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
        _ = 2 * Real.log T := by rw [Real.log_pow]; push_cast; ring
    calc |∫ t in a..b, mu t| ≤ CM * Real.log (2 * T + 4) * |b - a| := this
      _ ≤ CM * (2 * Real.log T) * 1 := by
          refine mul_le_mul ?_ hba (abs_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hlog24 hCM0.le
      _ = 2 * CM * Real.log T := by ring
  have hμ1 : |∫ t in T₁..T, mu t| ≤ 2 * CM * Real.log T :=
    hμwin T₁ T h1T₁ hT₁b (by linarith) (by rw [abs_of_nonneg (by linarith)]; linarith)
  have hμ2 : |∫ t in (2 * T)..T₂, mu t| ≤ 2 * CM * Real.log T :=
    hμwin (2 * T) T₂ (by linarith) hT₂a (by linarith) (by rw [abs_of_nonneg (by linarith)]; linarith)
  have hintmu := hCμ T (by linarith)
  have hT0 : (0:ℝ) < T := by linarith
  have hCμT : Cμ / T ≤ |Cμ| := by
    calc Cμ / T ≤ |Cμ| / T := by gcongr; exact le_abs_self _
      _ ≤ |Cμ| / 1 := by
          apply div_le_div_of_nonneg_left (abs_nonneg _) one_pos; linarith
      _ = |Cμ| := div_one _
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hπ3 : (3:ℝ) ≤ Real.pi := Real.pi_gt_three.le
  -- the key identity: N(T₁,T₂) = ∫μ + (1/π)·Rres
  have h5 : (Zc.N T₁ T₂ : ℝ) = (∫ t in T₁..T₂, mu t) + (1 / Real.pi) * Rres := by
    rw [hN, hRres, mul_sub, hgam]; ring
  have hkey : (Zc.N T (2 * T) : ℝ) - T * ell1 T / (2 * Real.pi)
      = (1 / Real.pi) * Rres
        + ((∫ t in T₁..T, mu t) + (∫ t in (2 * T)..T₂, mu t)
        + ((∫ t in T..(2 * T), mu t) - T * ell1 T / (2 * Real.pi)))
        - ((Zc.N T₁ T : ℝ) + (Zc.N (2 * T) T₂ : ℝ)) := by
    rw [hμsplit] at h5
    have h6 := hadd
    linarith
  have hA : |(1 / Real.pi) * Rres| ≤ 4 * CY * Real.log T + KY := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / Real.pi)]
    have hfrac : (1:ℝ) / Real.pi ≤ 1 := by rw [div_le_one hπ]; linarith
    have hnn : 0 ≤ 4 * CY * Real.log T + KY := by positivity
    calc 1 / Real.pi * |Rres| ≤ 1 / Real.pi * (4 * CY * Real.log T + KY) :=
          mul_le_mul_of_nonneg_left hYlog (by positivity)
      _ ≤ 1 * (4 * CY * Real.log T + KY) := mul_le_mul_of_nonneg_right hfrac hnn
      _ = 4 * CY * Real.log T + KY := one_mul _
  have hD : |(∫ t in T..(2 * T), mu t) - T * ell1 T / (2 * Real.pi)| ≤ |Cμ| * Real.log T := by
    calc |(∫ t in T..(2 * T), mu t) - T * ell1 T / (2 * Real.pi)| ≤ Cμ / T := hintmu
      _ ≤ |Cμ| := hCμT
      _ = |Cμ| * 1 := (mul_one _).symm
      _ ≤ |Cμ| * Real.log T := mul_le_mul_of_nonneg_left hlogT (abs_nonneg _)
  rw [show T / (2 * Real.pi) * ell1 T = T * ell1 T / (2 * Real.pi) by ring, hkey]
  have hNc1 : (0:ℝ) ≤ (Zc.N T₁ T : ℝ) := Nat.cast_nonneg _
  have hNc2 : (0:ℝ) ≤ (Zc.N (2 * T) T₂ : ℝ) := Nat.cast_nonneg _
  have htri : |(1 / Real.pi) * Rres
        + ((∫ t in T₁..T, mu t) + (∫ t in (2 * T)..T₂, mu t)
        + ((∫ t in T..(2 * T), mu t) - T * ell1 T / (2 * Real.pi)))
        - ((Zc.N T₁ T : ℝ) + (Zc.N (2 * T) T₂ : ℝ))|
      ≤ |(1 / Real.pi) * Rres|
        + (|∫ t in T₁..T, mu t| + |∫ t in (2 * T)..T₂, mu t|
        + |(∫ t in T..(2 * T), mu t) - T * ell1 T / (2 * Real.pi)|)
        + ((Zc.N T₁ T : ℝ) + (Zc.N (2 * T) T₂ : ℝ)) := by
    have t1 := abs_sub ((1 / Real.pi) * Rres
        + ((∫ t in T₁..T, mu t) + (∫ t in (2 * T)..T₂, mu t)
        + ((∫ t in T..(2 * T), mu t) - T * ell1 T / (2 * Real.pi))))
      ((Zc.N T₁ T : ℝ) + (Zc.N (2 * T) T₂ : ℝ))
    have t2 := abs_add_le ((1 / Real.pi) * Rres)
      ((∫ t in T₁..T, mu t) + (∫ t in (2 * T)..T₂, mu t)
        + ((∫ t in T..(2 * T), mu t) - T * ell1 T / (2 * Real.pi)))
    have t3 := abs_add_le ((∫ t in T₁..T, mu t) + (∫ t in (2 * T)..T₂, mu t))
      ((∫ t in T..(2 * T), mu t) - T * ell1 T / (2 * Real.pi))
    have t4 := abs_add_le (∫ t in T₁..T, mu t) (∫ t in (2 * T)..T₂, mu t)
    have t5 : |(Zc.N T₁ T : ℝ) + (Zc.N (2 * T) T₂ : ℝ)| = (Zc.N T₁ T : ℝ) + (Zc.N (2 * T) T₂ : ℝ) :=
      abs_of_nonneg (by positivity)
    linarith
  refine htri.trans ?_
  have hKY1 : KY ≤ KY * Real.log T := by nlinarith
  nlinarith [hA, hμ1, hμ2, hD, hw1, hw2, hCY.le, abs_nonneg Cμ, hCM0.le, hKY1]

end GenericRvM
end ZeroCount
end XiPrime
end Zeta23

end
