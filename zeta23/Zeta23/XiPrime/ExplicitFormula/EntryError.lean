/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/ExplicitFormula/EntryError.lean — the entry-error integral of the ξ′ explicit formula.
PURE REAL ANALYSIS, no ζ:  for a weight w (a two-bump product concentrated at
a, b ≥ T — in the application w(t) = H(5/4+it) = φ̂·φ̂ with bumps at τ_k, τ_l) and a function g
(in the application g = E′/E − B/(L⋆−A) on the line, from Expansion.lean) with
   ‖g‖ ≤ C_g everywhere  and  ‖g(t)‖ ≤ ε(|t − (a+b)/2| + 1) for t ≥ T/4,
   ‖w(t)‖ ≤ W·K_a(t)K_b(t),   (|t−a|+|t−b|)‖w(t)‖ ≤ W′·K_a(t)K_b(t),   K_c(t) := 1/(1+(t−c)²),
one gets  ‖∫ w·g‖ ≤ ε(W + W′/2)·8π/(4+(a−b)²) + C_g·W·16π/(9T²)   [XF′ Thm 4.2 proof (b),(c)].
The Cauchy convolution bound ∫ K_a K_b ≤ 8π/(4+(a−b)²) is the Δ⁻²-decay of the entry error.
-/
import Zeta23.XiPrime.ExplicitFormula
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Zeta23
namespace XiPrime

/-! ## 1. Cauchy kernels -/

/-- K_a(t) := 1/(1 + (t−a)²). -/
def cauchyK (a t : ℝ) : ℝ := (1 + (t - a) ^ 2)⁻¹

theorem cauchyK_pos (a t : ℝ) : 0 < cauchyK a t := by unfold cauchyK; positivity
theorem cauchyK_nonneg (a t : ℝ) : 0 ≤ cauchyK a t := (cauchyK_pos a t).le
theorem cauchyK_le_one (a t : ℝ) : cauchyK a t ≤ 1 := by
  unfold cauchyK; exact inv_le_one_of_one_le₀ (by nlinarith)

theorem continuous_cauchyK (a : ℝ) : Continuous (cauchyK a) := by
  unfold cauchyK
  exact Continuous.inv₀ (by fun_prop) (fun t => by positivity)

theorem integrable_cauchyK (a : ℝ) : Integrable (cauchyK a) := by
  have h := integrable_inv_one_add_sq.comp_sub_right a
  exact h

theorem integral_cauchyK (a : ℝ) : ∫ t, cauchyK a t = Real.pi := by
  unfold cauchyK
  rw [integral_sub_right_eq_self (fun t => (1 + t ^ 2)⁻¹) a]
  exact integral_univ_inv_one_add_sq

/-- the pointwise product bound behind the Δ⁻²-decay:
K_a K_b ≤ 4/(4+(a−b)²)·(K_a + K_b). -/
theorem cauchyK_mul_le (a b t : ℝ) :
    cauchyK a t * cauchyK b t ≤ 4 / (4 + (a - b) ^ 2) * (cauchyK a t + cauchyK b t) := by
  unfold cauchyK
  have hu : 0 < 1 + (t - a) ^ 2 := by positivity
  have hv : 0 < 1 + (t - b) ^ 2 := by positivity
  have hD : 0 < 4 + (a - b) ^ 2 := by positivity
  have key : (4 + (a - b) ^ 2) ≤ 4 * ((1 + (t - b) ^ 2) + (1 + (t - a) ^ 2)) := by
    nlinarith [sq_nonneg ((t - a) + (t - b)), sq_nonneg (t - a), sq_nonneg (t - b)]
  have eR : 4 / (4 + (a - b) ^ 2) * ((1 + (t - a) ^ 2)⁻¹ + (1 + (t - b) ^ 2)⁻¹)
      = (4 * ((1 + (t - b) ^ 2) + (1 + (t - a) ^ 2)))
        / ((4 + (a - b) ^ 2) * ((1 + (t - a) ^ 2) * (1 + (t - b) ^ 2))) := by
    field_simp
  have eL : (1 + (t - a) ^ 2)⁻¹ * (1 + (t - b) ^ 2)⁻¹
      = (4 + (a - b) ^ 2) / ((4 + (a - b) ^ 2) * ((1 + (t - a) ^ 2) * (1 + (t - b) ^ 2))) := by
    field_simp
  rw [eL, eR]
  exact div_le_div_of_nonneg_right key (by positivity)

theorem integrable_cauchyK_mul (a b : ℝ) : Integrable (fun t => cauchyK a t * cauchyK b t) := by
  refine (integrable_cauchyK a).mono' ((continuous_cauchyK a).mul (continuous_cauchyK b)).aestronglyMeasurable ?_
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (cauchyK_nonneg _ _) (cauchyK_nonneg _ _))]
  exact mul_le_of_le_one_right (cauchyK_nonneg _ _) (cauchyK_le_one _ _)

/-- **Cauchy convolution**: ∫ K_a K_b ≤ 8π/(4 + (a−b)²). -/
theorem integral_cauchyK_mul_le (a b : ℝ) :
    ∫ t, cauchyK a t * cauchyK b t ≤ 8 * Real.pi / (4 + (a - b) ^ 2) := by
  calc ∫ t, cauchyK a t * cauchyK b t
      ≤ ∫ t, 4 / (4 + (a - b) ^ 2) * (cauchyK a t + cauchyK b t) := by
        refine integral_mono (integrable_cauchyK_mul a b)
          (((integrable_cauchyK a).add (integrable_cauchyK b)).const_mul _) fun t => ?_
        exact cauchyK_mul_le a b t
    _ = 4 / (4 + (a - b) ^ 2) * (Real.pi + Real.pi) := by
        rw [integral_const_mul, integral_add (integrable_cauchyK a) (integrable_cauchyK b),
          integral_cauchyK, integral_cauchyK]
    _ = 8 * Real.pi / (4 + (a - b) ^ 2) := by ring

/-- far region: for a ≥ T > 0 and t ≤ T/4, K_a(t) ≤ 16/(9T²). -/
theorem cauchyK_far {a T t : ℝ} (hT : 0 < T) (ha : T ≤ a) (ht : t ≤ T / 4) :
    cauchyK a t ≤ 16 / (9 * T ^ 2) := by
  unfold cauchyK
  have h : (3 * T / 4) ^ 2 ≤ (t - a) ^ 2 := by
    have : 3 * T / 4 ≤ a - t := by linarith
    calc (3 * T / 4) ^ 2 ≤ (a - t) ^ 2 := pow_le_pow_left₀ (by positivity) this 2
      _ = (t - a) ^ 2 := by ring
  rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- ∫_{t ≤ T/4} K_a K_b ≤ 16π/(9T²) for a ≥ T > 0. -/
theorem setIntegral_cauchyK_mul_far {a b T : ℝ} (hT : 0 < T) (ha : T ≤ a) :
    ∫ t in Iic (T / 4), cauchyK a t * cauchyK b t ≤ 16 * Real.pi / (9 * T ^ 2) := by
  calc ∫ t in Iic (T / 4), cauchyK a t * cauchyK b t
      ≤ ∫ t in Iic (T / 4), 16 / (9 * T ^ 2) * cauchyK b t := by
        refine setIntegral_mono_on (integrable_cauchyK_mul a b).integrableOn
          ((integrable_cauchyK b).const_mul _).integrableOn measurableSet_Iic fun t ht => ?_
        exact mul_le_mul_of_nonneg_right (cauchyK_far hT ha ht) (cauchyK_nonneg _ _)
    _ ≤ ∫ t, 16 / (9 * T ^ 2) * cauchyK b t :=
        setIntegral_le_integral ((integrable_cauchyK b).const_mul _)
          (Eventually.of_forall fun t => mul_nonneg (by positivity) (cauchyK_nonneg _ _))
    _ = 16 * Real.pi / (9 * T ^ 2) := by rw [integral_const_mul, integral_cauchyK]; ring

/-! ## 2. The core entry-error estimate -/

/-- |t − (a+b)/2| ≤ (|t−a| + |t−b|)/2. -/
theorem abs_sub_midpoint_le (t a b : ℝ) : |t - (a + b) / 2| ≤ (|t - a| + |t - b|) / 2 := by
  have : t - (a + b) / 2 = ((t - a) + (t - b)) / 2 := by ring
  rw [this, abs_div, abs_two]
  exact div_le_div_of_nonneg_right (abs_add_le _ _) zero_le_two

/-- **core estimate** (see file header). -/
theorem entry_core {w g : ℝ → ℂ} {a b T ε Cg W W' : ℝ} (hT : 0 < T) (ha : T ≤ a) (hb : T ≤ b)
    (hwc : Continuous w) (hgc : Continuous g)
    (hε : 0 ≤ ε) (hCg : 0 ≤ Cg) (hW : 0 ≤ W) (hW' : 0 ≤ W')
    (hw : ∀ t, ‖w t‖ ≤ W * (cauchyK a t * cauchyK b t))
    (hw' : ∀ t, (|t - a| + |t - b|) * ‖w t‖ ≤ W' * (cauchyK a t * cauchyK b t))
    (hg : ∀ t, ‖g t‖ ≤ Cg)
    (hgε : ∀ t, T / 4 ≤ t → ‖g t‖ ≤ ε * (|t - (a + b) / 2| + 1)) :
    Integrable (fun t => w t * g t) ∧
    ‖∫ t, w t * g t‖
      ≤ ε * (W + W' / 2) * (8 * Real.pi / (4 + (a - b) ^ 2)) + Cg * W * (16 * Real.pi / (9 * T ^ 2)) := by
  -- the dominating function
  set F₁ : ℝ → ℝ := fun t => ε * (W + W' / 2) * (cauchyK a t * cauchyK b t) with hF₁
  set F₂ : ℝ → ℝ := fun t => (Iic (T / 4)).indicator (fun t => Cg * W * (cauchyK a t * cauchyK b t)) t
    with hF₂
  have hF₁i : Integrable F₁ := (integrable_cauchyK_mul a b).const_mul _
  have hF₂i : Integrable F₂ :=
    (((integrable_cauchyK_mul a b).const_mul (Cg * W)).integrableOn).integrable_indicator measurableSet_Iic
  have hdom : ∀ t, ‖w t * g t‖ ≤ F₁ t + F₂ t := by
    intro t
    have hK := mul_nonneg (cauchyK_nonneg a t) (cauchyK_nonneg b t)
    rw [norm_mul]
    rcases le_or_gt (T / 4) t with h | h
    · -- near region: use the ε bound
      have hF₂0 : 0 ≤ F₂ t := by
        simp only [hF₂]
        exact Set.indicator_nonneg (fun x _ => mul_nonneg (mul_nonneg hCg hW)
          (mul_nonneg (cauchyK_nonneg a x) (cauchyK_nonneg b x))) _
      have h1 : ‖w t‖ * ‖g t‖ ≤ ‖w t‖ * (ε * (|t - (a + b) / 2| + 1)) :=
        mul_le_mul_of_nonneg_left (hgε t h) (norm_nonneg _)
      have h2 : ‖w t‖ * (ε * (|t - (a + b) / 2| + 1))
          ≤ ε * ((|t - a| + |t - b|) / 2 * ‖w t‖ + ‖w t‖) := by
        have hm := abs_sub_midpoint_le t a b
        have h := mul_le_mul_of_nonneg_left (add_le_add_right hm 1) (mul_nonneg hε (norm_nonneg (w t)))
        have e1 : ‖w t‖ * (ε * (|t - (a + b) / 2| + 1)) = ε * ‖w t‖ * (|t - (a + b) / 2| + 1) := by ring
        have e2 : ε * ((|t - a| + |t - b|) / 2 * ‖w t‖ + ‖w t‖)
            = ε * ‖w t‖ * ((|t - a| + |t - b|) / 2 + 1) := by ring
        rw [e1, e2]; linarith
      have h3 : ε * ((|t - a| + |t - b|) / 2 * ‖w t‖ + ‖w t‖) ≤ F₁ t := by
        simp only [hF₁]
        have hA := hw' t
        have hB := hw t
        have e : ε * ((|t - a| + |t - b|) / 2 * ‖w t‖ + ‖w t‖)
            = ε * (((|t - a| + |t - b|) * ‖w t‖) / 2 + ‖w t‖) := by ring
        rw [e]
        have hsum : ((|t - a| + |t - b|) * ‖w t‖) / 2 + ‖w t‖
            ≤ (W' / 2 + W) * (cauchyK a t * cauchyK b t) := by nlinarith
        calc ε * (((|t - a| + |t - b|) * ‖w t‖) / 2 + ‖w t‖)
            ≤ ε * ((W' / 2 + W) * (cauchyK a t * cauchyK b t)) := mul_le_mul_of_nonneg_left hsum hε
          _ = ε * (W + W' / 2) * (cauchyK a t * cauchyK b t) := by ring
      linarith
    · -- far region: uniform bound
      have hmem : t ∈ Iic (T / 4) := h.le
      have hF₂t : F₂ t = Cg * W * (cauchyK a t * cauchyK b t) := by
        simp only [hF₂, Set.indicator_of_mem hmem]
      have hF₁0 : 0 ≤ F₁ t := by
        simp only [hF₁]
        exact mul_nonneg (mul_nonneg hε (by positivity)) hK
      have h1 : ‖w t‖ * ‖g t‖ ≤ W * (cauchyK a t * cauchyK b t) * Cg :=
        mul_le_mul (hw t) (hg t) (norm_nonneg _) (by positivity)
      rw [hF₂t]; linarith
  have hmeas : AEStronglyMeasurable (fun t => w t * g t) := (hwc.mul hgc).aestronglyMeasurable
  have hint : Integrable (fun t => w t * g t) :=
    (hF₁i.add hF₂i).mono' hmeas (Eventually.of_forall hdom)
  refine ⟨hint, ?_⟩
  calc ‖∫ t, w t * g t‖ ≤ ∫ t, F₁ t + F₂ t :=
        norm_integral_le_of_norm_le (hF₁i.add hF₂i) (Eventually.of_forall hdom)
    _ = (∫ t, F₁ t) + ∫ t, F₂ t := integral_add hF₁i hF₂i
    _ ≤ ε * (W + W' / 2) * (8 * Real.pi / (4 + (a - b) ^ 2)) + Cg * W * (16 * Real.pi / (9 * T ^ 2)) := by
        refine add_le_add ?_ ?_
        · simp only [hF₁]
          rw [integral_const_mul]
          exact mul_le_mul_of_nonneg_left (integral_cauchyK_mul_le a b) (by positivity)
        · simp only [hF₂]
          rw [integral_indicator measurableSet_Iic, integral_const_mul]
          exact mul_le_mul_of_nonneg_left (setIntegral_cauchyK_mul_far (b := b) hT ha) (by positivity)

/-- the mirrored core estimate: bumps at −a, −b and the ε-bound for t ≤ −T/4
(reduce to entry_core by t ↦ −t). -/
theorem entry_core_mirror {w g : ℝ → ℂ} {a b T ε Cg W W' : ℝ} (hT : 0 < T) (ha : T ≤ a) (hb : T ≤ b)
    (hwc : Continuous w) (hgc : Continuous g)
    (hε : 0 ≤ ε) (hCg : 0 ≤ Cg) (hW : 0 ≤ W) (hW' : 0 ≤ W')
    (hw : ∀ t, ‖w t‖ ≤ W * (cauchyK (-a) t * cauchyK (-b) t))
    (hw' : ∀ t, (|t + a| + |t + b|) * ‖w t‖ ≤ W' * (cauchyK (-a) t * cauchyK (-b) t))
    (hg : ∀ t, ‖g t‖ ≤ Cg)
    (hgε : ∀ t, t ≤ -(T / 4) → ‖g t‖ ≤ ε * (|t + (a + b) / 2| + 1)) :
    Integrable (fun t => w t * g t) ∧
    ‖∫ t, w t * g t‖
      ≤ ε * (W + W' / 2) * (8 * Real.pi / (4 + (a - b) ^ 2)) + Cg * W * (16 * Real.pi / (9 * T ^ 2)) := by
  have hK : ∀ c t : ℝ, cauchyK (-c) (-t) = cauchyK c t := by
    intro c t; unfold cauchyK; ring_nf
  have h := entry_core (w := fun t => w (-t)) (g := fun t => g (-t)) hT ha hb
    (hwc.comp continuous_neg) (hgc.comp continuous_neg) hε hCg hW hW'
    (fun t => by simpa [hK] using hw (-t))
    (fun t => by
      have := hw' (-t)
      simp only [hK] at this
      have e1 : |(-t) + a| = |t - a| := by rw [← abs_neg]; ring_nf
      have e2 : |(-t) + b| = |t - b| := by rw [← abs_neg]; ring_nf
      rwa [e1, e2] at this)
    (fun t => hg (-t))
    (fun t ht => by
      have := hgε (-t) (by linarith)
      have e : |(-t) + (a + b) / 2| = |t - (a + b) / 2| := by rw [← abs_neg]; ring_nf
      rwa [e] at this)
  obtain ⟨hint, hbound⟩ := h
  have hint' : Integrable (fun t => w t * g t) := by
    have := hint.comp_neg
    simpa using this
  refine ⟨hint', ?_⟩
  have e : ∫ t, w t * g t = ∫ t, w (-t) * g (-t) :=
    (integral_neg_eq_self (fun t => w t * g t) volume).symm
  rw [e]
  exact hbound

end XiPrime
end Zeta23
