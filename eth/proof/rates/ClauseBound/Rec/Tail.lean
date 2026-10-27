/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Field
import Mathlib.Probability.Moments.SubGaussian

/-! # Hoeffding's lemma on two points

`two_point_le`, in the namespace `ClauseBound.Rec.Tail`: p·e^{θ(1−p)} + (1−p)·e^{−θp} ≤ e^{θ²/8} for
0 ≤ p ≤ 1. This is Hoeffding's lemma for a random variable with values in {0, 1}.
It is taken from Mathlib's sub-Gaussian bound for a random variable with values in [0, 1], applied
to the measure with mass p at 1 and mass 1 − p at 0. -/

public section

open Finset

namespace ClauseBound.Rec

namespace Tail

/-- Hoeffding's lemma on two points: p·e^{θ(1−p)} + (1−p)·e^{−θp} ≤ e^{θ²/8} for 0 ≤ p ≤ 1. -/
theorem two_point_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (θ : ℝ) :
    p * Real.exp (θ * (1 - p)) + (1 - p) * Real.exp (θ * (0 - p)) ≤ Real.exp (θ ^ 2 / 8) := by
  open MeasureTheory ProbabilityTheory in
  let μ : Measure ℝ := ENNReal.ofReal p • Measure.dirac 1 + ENNReal.ofReal (1 - p) • Measure.dirac 0
  have hq0 : 0 ≤ 1 - p := by linarith
  have hprob : IsProbabilityMeasure μ := by
    constructor
    simp only [μ, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add hp0 hq0]
    simp
  have hint (f : ℝ → ℝ) : ∫ y, f y ∂μ = p * f 1 + (1 - p) * f 0 := by
    have h1 : Integrable f (ENNReal.ofReal p • Measure.dirac (1 : ℝ)) :=
      (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
    have h0 : Integrable f (ENNReal.ofReal (1 - p) • Measure.dirac (0 : ℝ)) :=
      (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
    rw [integral_add_measure h1 h0, integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac,
      ENNReal.toReal_ofReal hp0, ENNReal.toReal_ofReal hq0]
    simp
  have hb : ∀ᵐ y ∂μ, id y ∈ Set.Icc (0 : ℝ) 1 := by
    simp only [μ]
    rw [ae_add_measure_iff]
    constructor
    · refine Measure.ae_smul_measure ?_ _
      rw [ae_dirac_eq]
      simp
    · refine Measure.ae_smul_measure ?_ _
      rw [ae_dirac_eq]
      simp
  have h := (hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := id) aemeasurable_id hb).mgf_le θ
  have hmean : ∫ y, id y ∂μ = p := by rw [hint]; simp
  rw [hmean, mgf, hint] at h
  refine h.trans (le_of_eq ?_)
  congr 1
  simp
  ring

end Tail

open Tail

end ClauseBound.Rec
