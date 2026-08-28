/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
Zeta23/Defs/LeafIntegrals.lean — self-contained elementary integral bounds used as drop-ins by
§5's lem:ends (Zeta23/PrimeSideA/EndsE1.lean). Imports only Mathlib.
-/

open MeasureTheory Real Set

noncomputable section

namespace Zeta23.LeafIntegrals

/-- ∫_T^{2T} ((1+(τ−T))²)⁻¹ dτ = 1 − 1/(1+T) ≤ 1 -/
lemma integral_left (T : ℝ) (hT : 0 < T) :
    ∫ τ in T..(2 * T), ((1 + (τ - T)) ^ 2)⁻¹ ≤ 1 := by
  have hderiv : ∀ x ∈ uIcc T (2 * T),
      HasDerivAt (fun τ : ℝ => -(1 + (τ - T))⁻¹) (((1 + (x - T)) ^ 2)⁻¹) x := by
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    have hpos : (1 + (x - T)) ≠ 0 := by linarith [hx.1]
    have h1 : HasDerivAt (fun τ : ℝ => 1 + (τ - T)) 1 x := by
      simpa using ((hasDerivAt_id x).sub_const T).const_add 1
    have h2 := (h1.inv hpos).neg
    have heq : -(-1 / (1 + (x - T)) ^ 2) = ((1 + (x - T)) ^ 2)⁻¹ := by
      rw [neg_div, neg_neg, one_div]
    exact heq ▸ h2
  have hcont : ContinuousOn (fun x : ℝ => ((1 + (x - T)) ^ 2)⁻¹) (uIcc T (2 * T)) := by
    rw [uIcc_of_le (by linarith)]
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx; have : 0 < 1 + (x - T) := by linarith [hx.1]
    positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  have h1T : 0 < 1 + T := by linarith
  simp only [sub_self, add_zero, inv_one]
  rw [show 2 * T - T = T by ring]
  have : 0 < (1 + T)⁻¹ := by positivity
  linarith

/-- ∫_T^{2T} ((1+(2T−τ))²)⁻¹ dτ = 1 − 1/(1+T) ≤ 1 -/
lemma integral_right (T : ℝ) (hT : 0 < T) :
    ∫ τ in T..(2 * T), ((1 + (2 * T - τ)) ^ 2)⁻¹ ≤ 1 := by
  have hderiv : ∀ x ∈ uIcc T (2 * T),
      HasDerivAt (fun τ : ℝ => (1 + (2 * T - τ))⁻¹) (((1 + (2 * T - x)) ^ 2)⁻¹) x := by
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    have hpos : (1 + (2 * T - x)) ≠ 0 := by linarith [hx.2]
    have h1 : HasDerivAt (fun τ : ℝ => 1 + (2 * T - τ)) (-1) x := by
      simpa using ((hasDerivAt_id x).const_sub (2 * T)).const_add 1
    have h2 := h1.inv hpos
    have heq : -(-1) / (1 + (2 * T - x)) ^ 2 = ((1 + (2 * T - x)) ^ 2)⁻¹ := by
      rw [neg_neg, one_div]
    exact heq ▸ h2
  have hcont : ContinuousOn (fun x : ℝ => ((1 + (2 * T - x)) ^ 2)⁻¹) (uIcc T (2 * T)) := by
    rw [uIcc_of_le (by linarith)]
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx; have : 0 < 1 + (2 * T - x) := by linarith [hx.2]
    positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  have h1T : 0 < 1 + T := by linarith
  rw [show 2 * T - 2 * T = (0:ℝ) by ring, show 2 * T - T = T by ring]
  simp only [add_zero, inv_one]
  have : 0 < (1 + T)⁻¹ := by positivity
  linarith

/-- the (Ig) core: ∫_{[T,2T]} (1 + min(τ−T, 2T−τ))⁻² dτ ≤ 2. -/
theorem Ig_core (T : ℝ) (hT : 0 < T) :
    ∫ τ in Icc T (2 * T), ((1 + min (τ - T) (2 * T - τ)) ^ 2)⁻¹ ≤ 2 := by
  have hle : T ≤ 2 * T := by linarith
  -- pointwise bound on [T,2T]
  have hpt : ∀ τ ∈ Icc T (2 * T), ((1 + min (τ - T) (2 * T - τ)) ^ 2)⁻¹ ≤
      ((1 + (τ - T)) ^ 2)⁻¹ + ((1 + (2 * T - τ)) ^ 2)⁻¹ := by
    intro τ hτ
    have ha : 0 < 1 + (τ - T) := by linarith [hτ.1]
    have hb : 0 < 1 + (2 * T - τ) := by linarith [hτ.2]
    have hA : 0 ≤ ((1 + (τ - T)) ^ 2)⁻¹ := by positivity
    have hB : 0 ≤ ((1 + (2 * T - τ)) ^ 2)⁻¹ := by positivity
    rcases min_choice (τ - T) (2 * T - τ) with h | h <;> rw [h] <;> linarith
  have hcontL : ContinuousOn (fun τ : ℝ => ((1 + (τ - T)) ^ 2)⁻¹) (Icc T (2 * T)) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx; have : 0 < 1 + (x - T) := by linarith [hx.1]
    positivity
  have hcontR : ContinuousOn (fun τ : ℝ => ((1 + (2 * T - τ)) ^ 2)⁻¹) (Icc T (2 * T)) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx; have : 0 < 1 + (2 * T - x) := by linarith [hx.2]
    positivity
  have hcontM : ContinuousOn (fun τ : ℝ => ((1 + min (τ - T) (2 * T - τ)) ^ 2)⁻¹) (Icc T (2 * T)) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx
    have : 0 < 1 + min (x - T) (2 * T - x) := by
      rcases min_choice (x - T) (2 * T - x) with h | h <;> rw [h] <;> linarith [hx.1, hx.2]
    positivity
  calc ∫ τ in Icc T (2 * T), ((1 + min (τ - T) (2 * T - τ)) ^ 2)⁻¹
      ≤ ∫ τ in Icc T (2 * T), (((1 + (τ - T)) ^ 2)⁻¹ + ((1 + (2 * T - τ)) ^ 2)⁻¹) := by
        apply setIntegral_mono_on (hcontM.integrableOn_Icc) ((hcontL.add hcontR).integrableOn_Icc)
          measurableSet_Icc hpt
    _ = (∫ τ in T..(2 * T), ((1 + (τ - T)) ^ 2)⁻¹) + ∫ τ in T..(2 * T), ((1 + (2 * T - τ)) ^ 2)⁻¹ := by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle,
          intervalIntegral.integral_add (hcontL.intervalIntegrable_of_Icc hle)
            (hcontR.intervalIntegrable_of_Icc hle)]
    _ ≤ 1 + 1 := add_le_add (integral_left T hT) (integral_right T hT)
    _ = 2 := by norm_num

/-! ## (W3) core: ∫ ψ(r)² (2+|r|)² dr ≤ 18 L² + 18 (c/w)² for any even 0 ≤ ψ ≤ L with ψ(r) ≤ c/(w r²) -/

/-- Abstract form of lem:ends' leaf (W3): for ψ : ℝ → ℝ with ψ(|r|) = ψ(r), 0 ≤ ψ ≤ L,
ψ(r) ≤ c/(w r²) (r ≠ 0) and ψ² integrable:  ψ²(2+|r|)² is integrable and
∫ ψ(r)²(2+|r|)² dr ≤ 18L² + 18(c/w)²  (majorant 9L² on |r| ≤ 1, 9(c/w)²/r² on |r| ≥ 1). -/
theorem W3_core (ψ : ℝ → ℝ) (L c w : ℝ) (hw : 0 < w)
    (habs : ∀ r, ψ |r| = ψ r) (hnn : ∀ r, 0 ≤ ψ r) (hleL : ∀ r, ψ r ≤ L)
    (hdecay : ∀ r, r ≠ 0 → ψ r ≤ c / (w * r ^ 2)) (hint : Integrable (fun r => ψ r ^ 2)) :
    Integrable (fun r => ψ r ^ 2 * (2 + |r|) ^ 2) ∧
    ∫ r, ψ r ^ 2 * (2 + |r|) ^ 2 ≤ 18 * L ^ 2 + 18 * (c / w) ^ 2 := by
  have hK : 0 ≤ (c / w) ^ 2 := sq_nonneg _
  -- pointwise bounds
  have hP1 : ∀ r : ℝ, |r| ≤ 1 → ψ r ^ 2 * (2 + |r|) ^ 2 ≤ 9 * L ^ 2 := by
    intro r hr
    have h1 : ψ r ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (hnn r) (hleL r) 2
    have h2 : (2 + |r|) ^ 2 ≤ 9 := by nlinarith [abs_nonneg r]
    nlinarith [sq_nonneg (ψ r), sq_nonneg (2 + |r|)]
  have hP2 : ∀ r : ℝ, 1 ≤ |r| → ψ r ^ 2 * (2 + |r|) ^ 2 ≤ 9 * (c / w) ^ 2 * (r ^ 2)⁻¹ := by
    intro r hr
    have hr0 : r ≠ 0 := by intro h; rw [h, abs_zero] at hr; linarith
    have hr2 : 0 < r ^ 2 := by positivity
    have hψ : ψ r ≤ c / w * (r ^ 2)⁻¹ := by
      have := hdecay r hr0; rwa [show c / (w * r ^ 2) = c / w * (r ^ 2)⁻¹ by field_simp] at this
    have hψ0 := hnn r
    have h1 : ψ r ^ 2 ≤ (c / w) ^ 2 * (r ^ 2)⁻¹ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hψ0 hψ 2
    have h2 : (2 + |r|) ^ 2 ≤ 9 * r ^ 2 := by
      have : r ^ 2 = |r| ^ 2 := (sq_abs r).symm
      rw [this]; nlinarith
    calc ψ r ^ 2 * (2 + |r|) ^ 2 ≤ ((c / w) ^ 2 * (r ^ 2)⁻¹ ^ 2) * (9 * r ^ 2) :=
          mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
      _ = 9 * (c / w) ^ 2 * (r ^ 2)⁻¹ := by field_simp
  -- integrable majorant 18 (L² + (c/w)²) / (1 + r²)
  have hmaj : ∀ r : ℝ, ψ r ^ 2 * (2 + |r|) ^ 2 ≤ 18 * (L ^ 2 + (c / w) ^ 2) * (1 + r ^ 2)⁻¹ := by
    intro r
    have h1r : 0 < 1 + r ^ 2 := by positivity
    rcases le_or_gt |r| 1 with hr | hr
    · have hf := hP1 r hr
      have : r ^ 2 ≤ 1 := by have := (sq_abs r).symm; nlinarith [abs_nonneg r]
      rw [← div_eq_mul_inv, le_div_iff₀ h1r]
      nlinarith
    · have hf := hP2 r hr.le
      have hr2 : 1 ≤ r ^ 2 := by have := (sq_abs r).symm; nlinarith
      have hrpos : 0 < r ^ 2 := by positivity
      rw [← div_eq_mul_inv, le_div_iff₀ h1r]
      rw [← div_eq_mul_inv, le_div_iff₀ hrpos] at hf
      nlinarith
  have hmeas : AEStronglyMeasurable (fun r => ψ r ^ 2 * (2 + |r|) ^ 2) volume :=
    hint.aestronglyMeasurable.mul (by fun_prop : Continuous fun r : ℝ => (2 + |r|) ^ 2).aestronglyMeasurable
  have hInt : Integrable (fun r => ψ r ^ 2 * (2 + |r|) ^ 2) := by
    refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (18 * (L ^ 2 + (c / w) ^ 2))) hmeas
      (Filter.Eventually.of_forall fun r => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hmaj r
  refine ⟨hInt, ?_⟩
  -- reduce to (0, ∞) by evenness
  set g : ℝ → ℝ := fun u => ψ u ^ 2 * (2 + u) ^ 2 with hg
  have hfg : (fun r => ψ r ^ 2 * (2 + |r|) ^ 2) = fun r => g |r| := by
    funext r; simp only [hg, habs]
  rw [hfg, integral_comp_abs]
  have hgInt : IntegrableOn g (Ioi 0) := by
    refine IntegrableOn.congr_fun hInt.integrableOn (fun u hu => ?_) measurableSet_Ioi
    simp only [hg, abs_of_pos (mem_Ioi.mp hu)]
  -- split (0,∞) = (0,1] ∪ (1,∞)
  have hsplit : ∫ u in Ioi (0:ℝ), g u = (∫ u in Ioc (0:ℝ) 1, g u) + ∫ u in Ioi (1:ℝ), g u := by
    rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        (hgInt.mono_set Ioc_subset_Ioi_self) (hgInt.mono_set (Ioi_subset_Ioi zero_le_one))]
  have hJ1 : ∫ u in Ioc (0:ℝ) 1, g u ≤ 9 * L ^ 2 := by
    have h := setIntegral_mono_on (hgInt.mono_set Ioc_subset_Ioi_self)
      (integrableOn_const (μ := volume) (s := Ioc (0:ℝ) 1) (C := 9 * L ^ 2) (by simp))
      measurableSet_Ioc
      (fun u hu => by
        have hu1 : |u| ≤ 1 := by rw [abs_of_pos hu.1]; exact hu.2
        simpa only [hg, abs_of_pos hu.1] using hP1 u hu1)
    simpa using h
  have hJ2 : ∫ u in Ioi (1:ℝ), g u ≤ 9 * (c / w) ^ 2 := by
    have hrp : IntegrableOn (fun u : ℝ => 9 * (c / w) ^ 2 * u ^ (-2:ℝ)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul _
    have h := setIntegral_mono_on (hgInt.mono_set (Ioi_subset_Ioi zero_le_one)) hrp
      measurableSet_Ioi
      (fun u hu => by
        have hu0 : 0 < u := lt_trans one_pos hu
        have hu1 : 1 ≤ |u| := by rw [abs_of_pos hu0]; exact hu.le
        have := hP2 u hu1
        simp only [hg]
        rw [abs_of_pos hu0] at this
        rwa [Real.rpow_neg hu0.le, Real.rpow_two])
    refine h.trans (le_of_eq ?_)
    rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) one_pos]
    norm_num
  linarith

end Zeta23.LeafIntegrals
