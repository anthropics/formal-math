/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/PrimeSideA/MuMu.lean

[prop:mumu] (paper §5.4): 𝓜[μ,μ] = 2πbL ∫_T^{2T} μ² + O(l² log L).

Paper proof, as implemented here:
  * shear τ = τ' + x (`sqIntegral_shear`):
      𝓜[μ,μ] = ∫_ℝ Φ(x)² (∫_{I∩(I−x)} μ(x+τ')μ(τ') dτ') dx;
  * Lipschitz step "μ(τ)=μ(τ')+O(|τ−τ'|/T)" (via `mu_increment_bound`'s (K|r|+10r²)/t):
      |∫_{Ix}(μ(x+τ')−μ(τ'))μ(τ')| ≤ l(K|x| + 10x²)   (window length ≤ T, τ' ≥ T);
  * completing ∫_{Ix} to ∫_I ("∫_{I−τ'}Φ² = 2πbL − tails"):
      |∫_{I∖Ix} μ²| ≤ l²·|x|   (vol(I∖Ix) = min(|x|,T));
  * ∫Φ²|x| ≤ 8 + 8log(cϱL/4w) ≪ log L  [eq:psiints]  and  ∫Φ²x² ≤ 8 + 2(cϱ/w)² = O(1).
-/
import Zeta23.PrimeSideA.Basic
import Zeta23.PrimeSideB.PPKernel

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Real Set
open scoped BigOperators

namespace Zeta23
namespace PrimeSide

variable {cϱ : ℝ}

section Core

variable {p : Setting} {F : LocalFun}

/-- Core scalar estimate: for every x, the inner shear integral differs from `∫_I μ²` by at most
`(1+K) l² |x| + 10 l x²`. -/
theorem abs_inner_sub_le (hΓ : Zeta23.GammaFacts) (hF : LocalHypsCore cϱ p F) (hT2 : 2 ≤ p.T)
    (hμl : ∀ τ ∈ Icc p.T (2 * p.T), |Zeta23.mu τ| ≤ p.l)
    {K : ℝ} (hK0 : 0 ≤ K)
    (hKinc : ∀ t : ℝ, 2 ≤ t → ∀ r : ℝ,
      |Zeta23.mu (t + r) - Zeta23.mu t| ≤ (K * |r| + 10 * r ^ 2) / t)
    (x : ℝ) :
    |(∫ τ' in Ix p.T x, Zeta23.mu (x + τ') * Zeta23.mu τ')
        - ∫ τ' in Icc p.T (2 * p.T), Zeta23.mu τ' ^ 2|
      ≤ (1 + K) * p.l ^ 2 * |x| + 10 * p.l * x ^ 2 := by
  have hμc : Continuous Zeta23.mu := hΓ.smooth.continuous
  have hT0 : (0 : ℝ) < p.T := by linarith
  have hl1 : 1 ≤ p.l := hF.one_le_l
  have hl0 : (0 : ℝ) ≤ p.l := by linarith
  have hcnn : 0 ≤ ∫ τ' in Icc p.T (2 * p.T), Zeta23.mu τ' ^ 2 :=
    setIntegral_nonneg measurableSet_Icc fun τ' _ => sq_nonneg _
  have hsq_bound : ∀ τ' ∈ Icc p.T (2 * p.T), ‖Zeta23.mu τ' ^ 2‖ ≤ p.l ^ 2 := by
    intro τ' hτ'
    have h := hμl τ' hτ'
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [abs_nonneg (Zeta23.mu τ'), sq_abs (Zeta23.mu τ')]
  have hcle : ∫ τ' in Icc p.T (2 * p.T), Zeta23.mu τ' ^ 2 ≤ p.l ^ 2 * p.T := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc p.T (2 * p.T))
      (f := fun τ' => Zeta23.mu τ' ^ 2)
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top) hsq_bound
    rw [Real.norm_eq_abs, abs_of_nonneg hcnn, measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith), show 2 * p.T - p.T = p.T by ring] at h
    exact h
  rcases le_or_gt |x| p.T with hx | hx
  · -- |x| ≤ T
    have hIle : max (p.T - x) p.T ≤ min (2 * p.T - x) (2 * p.T) := Ix_le hT0.le hx
    have hlen : min (2 * p.T - x) (2 * p.T) - max (p.T - x) p.T = p.T - |x| :=
      Ix_length
    have hIxI : Ix p.T x ⊆ Icc p.T (2 * p.T) := fun τ' hτ' => (mem_Ix.mp hτ').2
    have hIxcompact : IsCompact (Ix p.T x) := by unfold Ix; exact isCompact_Icc
    have hIxmeas : MeasurableSet (Ix p.T x) := measurableSet_Ix p.T x
    have hIxfin : volume (Ix p.T x) ≠ ⊤ := by
      unfold Ix; rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    have hIxvol : (volume : Measure ℝ).real (Ix p.T x) = p.T - |x| := by
      unfold Ix
      rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
      linarith
    have hIxInt1 : IntegrableOn (fun τ' => Zeta23.mu (x + τ') * Zeta23.mu τ') (Ix p.T x) :=
      ContinuousOn.integrableOn_compact hIxcompact (by fun_prop)
    have hIxInt2 : IntegrableOn (fun τ' => Zeta23.mu τ' ^ 2) (Ix p.T x) :=
      ContinuousOn.integrableOn_compact hIxcompact (by fun_prop)
    have hIInt2 : IntegrableOn (fun τ' => Zeta23.mu τ' ^ 2) (Icc p.T (2 * p.T)) :=
      ContinuousOn.integrableOn_compact isCompact_Icc (by fun_prop)
    -- Lipschitz piece
    have hlip : |(∫ τ' in Ix p.T x, Zeta23.mu (x + τ') * Zeta23.mu τ')
        - ∫ τ' in Ix p.T x, Zeta23.mu τ' ^ 2| ≤ p.l * (K * |x| + 10 * x ^ 2) := by
      rw [← integral_sub hIxInt1 hIxInt2]
      have hb : ∀ τ' ∈ Ix p.T x,
          ‖Zeta23.mu (x + τ') * Zeta23.mu τ' - Zeta23.mu τ' ^ 2‖
            ≤ (K * |x| + 10 * x ^ 2) / p.T * p.l := by
        intro τ' hτ'
        obtain ⟨_, hmem2⟩ := mem_Ix.mp hτ'
        have hτT : p.T ≤ τ' := hmem2.1
        have h2τ : 2 ≤ τ' := by linarith
        have hinc := hKinc τ' h2τ x
        rw [show τ' + x = x + τ' by ring] at hinc
        have hμτ : |Zeta23.mu τ'| ≤ p.l := hμl τ' hmem2
        have hq : (K * |x| + 10 * x ^ 2) / τ' ≤ (K * |x| + 10 * x ^ 2) / p.T := by
          gcongr
        calc ‖Zeta23.mu (x + τ') * Zeta23.mu τ' - Zeta23.mu τ' ^ 2‖
            = |Zeta23.mu (x + τ') - Zeta23.mu τ'| * |Zeta23.mu τ'| := by
              rw [Real.norm_eq_abs, ← abs_mul]; congr 1; ring
          _ ≤ (K * |x| + 10 * x ^ 2) / p.T * p.l :=
              mul_le_mul (hinc.trans hq) hμτ (abs_nonneg _) (by positivity)
      have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ix p.T x)
        (f := fun τ' => Zeta23.mu (x + τ') * Zeta23.mu τ' - Zeta23.mu τ' ^ 2)
        (lt_of_le_of_ne (le_top) hIxfin) hb
      rw [Real.norm_eq_abs, hIxvol] at h
      refine h.trans ?_
      have hfrac : (p.T - |x|) / p.T ≤ 1 := by
        rw [div_le_one hT0]; linarith [abs_nonneg x]
      have hnum : (0 : ℝ) ≤ K * |x| + 10 * x ^ 2 := by positivity
      calc (K * |x| + 10 * x ^ 2) / p.T * p.l * (p.T - |x|)
          = p.l * (K * |x| + 10 * x ^ 2) * ((p.T - |x|) / p.T) := by ring
        _ ≤ p.l * (K * |x| + 10 * x ^ 2) * 1 := by
            have : (0 : ℝ) ≤ p.l * (K * |x| + 10 * x ^ 2) := by positivity
            exact mul_le_mul_of_nonneg_left hfrac this
        _ = p.l * (K * |x| + 10 * x ^ 2) := mul_one _
    -- completion piece
    have hcomp : |(∫ τ' in Ix p.T x, Zeta23.mu τ' ^ 2)
        - ∫ τ' in Icc p.T (2 * p.T), Zeta23.mu τ' ^ 2| ≤ p.l ^ 2 * |x| := by
      rw [abs_sub_comm, ← setIntegral_sdiff hIxmeas hIInt2 hIxI]
      have hdvol : (volume : Measure ℝ).real (Icc p.T (2 * p.T) \ Ix p.T x) = |x| := by
        have hsub : volume (Icc p.T (2 * p.T) \ Ix p.T x)
            = volume (Icc p.T (2 * p.T)) - volume (Ix p.T x) :=
          measure_sdiff hIxI hIxmeas.nullMeasurableSet hIxfin
        rw [measureReal_def, hsub]
        unfold Ix
        rw [Real.volume_Icc, Real.volume_Icc,
          ← ENNReal.ofReal_sub _ (by linarith :
            (0 : ℝ) ≤ min (2 * p.T - x) (2 * p.T) - max (p.T - x) p.T),
          ENNReal.toReal_ofReal (by linarith [abs_nonneg x])]
        linarith
      have hb : ∀ τ' ∈ Icc p.T (2 * p.T) \ Ix p.T x, ‖Zeta23.mu τ' ^ 2‖ ≤ p.l ^ 2 :=
        fun τ' hτ' => hsq_bound τ' hτ'.1
      have h := norm_setIntegral_le_of_norm_le_const (μ := volume)
        (s := Icc p.T (2 * p.T) \ Ix p.T x) (f := fun τ' => Zeta23.mu τ' ^ 2)
        (lt_of_le_of_lt (measure_mono Set.sdiff_subset)
          (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)) hb
      rw [Real.norm_eq_abs, hdvol] at h
      exact h
    refine (abs_sub_le _ (∫ τ' in Ix p.T x, Zeta23.mu τ' ^ 2) _).trans ?_
    refine (add_le_add hlip hcomp).trans ?_
    nlinarith [abs_nonneg x, sq_nonneg x,
      mul_nonneg (mul_nonneg hK0 hl0) (abs_nonneg x),
      mul_nonneg (mul_nonneg hK0 (mul_nonneg hl0 hl0)) (abs_nonneg x)]
  · -- |x| > T: the window is empty, the main term itself is ≤ l²T ≤ l²|x|
    rw [Ix_eq_empty hT0.le hx, Measure.restrict_empty, integral_zero_measure, zero_sub,
      abs_neg, abs_of_nonneg hcnn]
    refine hcle.trans ?_
    nlinarith [mul_nonneg (sq_nonneg p.l) (by linarith : (0 : ℝ) ≤ |x| - p.T),
      mul_nonneg (mul_nonneg hK0 (sq_nonneg p.l)) (abs_nonneg x),
      mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 10) hl0) (sq_nonneg x)]

/-- **Core estimate of [prop:mumu]** at fixed (p, F), error in terms of the two Φ-integrals. -/
theorem mumu_core (hΓ : Zeta23.GammaFacts) (hF : LocalHypsCore cϱ p F) (hT2 : 2 ≤ p.T)
    (hμl : ∀ τ ∈ Icc p.T (2 * p.T), |Zeta23.mu τ| ≤ p.l)
    {K : ℝ} (hK0 : 0 ≤ K)
    (hKinc : ∀ t : ℝ, 2 ≤ t → ∀ r : ℝ,
      |Zeta23.mu (t + r) - Zeta23.mu t| ≤ (K * |r| + 10 * r ^ 2) / t) :
    |Mform F.Phi p.T Zeta23.mu Zeta23.mu
        - 2 * π * F.b * p.L * ∫ τ in p.T..(2 * p.T), Zeta23.mu τ ^ 2|
      ≤ (1 + K) * p.l ^ 2 * (∫ x, F.Phi x ^ 2 * |x|)
        + 10 * p.l * ∫ x, F.Phi x ^ 2 * x ^ 2 := by
  have hμc : Continuous Zeta23.mu := hΓ.smooth.continuous
  have hΦc : Continuous F.Phi := hF.Phi_contDiff.continuous
  have hGc : Continuous fun q : ℝ × ℝ => Zeta23.mu q.1 * Zeta23.mu q.2 := by fun_prop
  set c : ℝ := ∫ τ' in Icc p.T (2 * p.T), Zeta23.mu τ' ^ 2 with hc
  have hc' : ∫ τ in p.T..(2 * p.T), Zeta23.mu τ ^ 2 = c := by
    rw [intervalIntegral.integral_of_le (by linarith), hc, integral_Icc_eq_integral_Ioc]
  have hshear : Mform F.Phi p.T Zeta23.mu Zeta23.mu
      = ∫ x, F.Phi x ^ 2 * ∫ τ' in Ix p.T x, Zeta23.mu (x + τ') * Zeta23.mu τ' := by
    unfold Mform
    simp only [mul_assoc]
    exact sqIntegral_shear hΦc hGc
  have hfInt : Integrable (fun x => F.Phi x ^ 2 * ∫ τ' in Ix p.T x,
      Zeta23.mu (x + τ') * Zeta23.mu τ') := integrable_sq_mul_inner hΦc hGc
  have hgInt : Integrable (fun x => F.Phi x ^ 2 * c) := hF.Phi_sq_integrable.mul_const c
  have hmain : 2 * π * F.b * p.L * c = ∫ x, F.Phi x ^ 2 * c := by
    rw [integral_mul_const c (fun x => F.Phi x ^ 2), hF.Phi_sq_integral]
  rw [hc', hshear, hmain, ← integral_sub hfInt hgInt]
  have hpt : ∀ x : ℝ, |F.Phi x ^ 2 * (∫ τ' in Ix p.T x, Zeta23.mu (x + τ') * Zeta23.mu τ')
      - F.Phi x ^ 2 * c|
      ≤ (1 + K) * p.l ^ 2 * (F.Phi x ^ 2 * |x|) + 10 * p.l * (F.Phi x ^ 2 * x ^ 2) := by
    intro x
    rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg (F.Phi x))]
    have hinner := abs_inner_sub_le hΓ hF hT2 hμl hK0 hKinc x
    rw [← hc] at hinner
    calc F.Phi x ^ 2 * |(∫ τ' in Ix p.T x, Zeta23.mu (x + τ') * Zeta23.mu τ') - c|
        ≤ F.Phi x ^ 2 * ((1 + K) * p.l ^ 2 * |x| + 10 * p.l * x ^ 2) := by
          gcongr
      _ = (1 + K) * p.l ^ 2 * (F.Phi x ^ 2 * |x|) + 10 * p.l * (F.Phi x ^ 2 * x ^ 2) := by ring
  calc |∫ x, (F.Phi x ^ 2 * (∫ τ' in Ix p.T x, Zeta23.mu (x + τ') * Zeta23.mu τ')
        - F.Phi x ^ 2 * c)|
      ≤ ∫ x, |F.Phi x ^ 2 * (∫ τ' in Ix p.T x, Zeta23.mu (x + τ') * Zeta23.mu τ')
        - F.Phi x ^ 2 * c| := by
        rw [← Real.norm_eq_abs]
        refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
        simp_rw [Real.norm_eq_abs]
    _ ≤ ∫ x, ((1 + K) * p.l ^ 2 * (F.Phi x ^ 2 * |x|) + 10 * p.l * (F.Phi x ^ 2 * x ^ 2)) :=
        integral_mono (hfInt.sub hgInt).abs
          ((hF.Phi_sq_mul_abs_integrable.const_mul _).add
            (hF.Phi_sq_mul_sq_integrable.const_mul _)) hpt
    _ = (1 + K) * p.l ^ 2 * (∫ x, F.Phi x ^ 2 * |x|)
        + 10 * p.l * ∫ x, F.Phi x ^ 2 * x ^ 2 := by
        rw [integral_add (hF.Phi_sq_mul_abs_integrable.const_mul _)
          (hF.Phi_sq_mul_sq_integrable.const_mul _),
          integral_const_mul, integral_const_mul]

end Core

/-! ## [prop:mumu] -/

variable (cϱ lam : ℝ)

set_option linter.unusedVariables false in
/-- **[prop:mumu]** (§5.4): `𝓜[μ,μ] = 2πbL ∫_T^{2T} μ² + O(l² log L)`.
(`hcheb`/`hlam` are unused here but kept so that the statement matches the fixed interface
shared with the other prime-side propositions.) -/
theorem prop_mumu (hΓ : Zeta23.GammaFacts) (hcheb : Zeta23.ChebyshevMertens)
    (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAtCore cϱ lam (fun p F =>
      |Mform F.Phi p.T Zeta23.mu Zeta23.mu
          - 2 * π * F.b * p.L * ∫ τ in p.T..(2 * p.T), Zeta23.mu τ ^ 2|
        ≤ C * (p.l ^ 2 * Real.log p.L)) := by
  obtain ⟨K, hK0, hKinc⟩ := mu_increment_bound hΓ
  obtain ⟨T₀μ, hT₀μ⟩ := mu_abs_le_l hΓ
  refine ⟨(1 + K) * (12 + 4 * max 0 (Real.log cϱ)) + 5 * (8 + 2 * cϱ ^ 2),
    max T₀μ 2, fun p F hplam hT hF => ?_⟩
  have hT2 : 2 ≤ p.T := le_trans (le_max_right _ _) hT
  have hμl := hT₀μ p (le_trans (le_max_left _ _) hT)
  have hcore := mumu_core hΓ hF hT2 hμl hK0 hKinc
  have hI1 := hF.integral_Phi_sq_mul_abs_le
  have hI2 := hF.integral_Phi_sq_mul_sq_le
  have hL8 : 8 ≤ p.L := hF.eight_le_L
  have hlog2 : 2 ≤ Real.log p.L := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have h1 := Real.exp_one_lt_d9
    calc Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      _ ≤ 2.7182818286 * 2.7182818286 := by nlinarith [Real.exp_pos 1]
      _ ≤ 8 := by norm_num
      _ ≤ p.L := hL8
  have hlogpos : 0 < Real.log p.L := by linarith
  have hcϱ4 : 4 ≤ cϱ := hF.four_le_cϱ
  have hw1 : 1 ≤ p.w := hF.one_le_w
  have hl1 : 1 ≤ p.l := hF.one_le_l
  have hm0 : 0 ≤ max 0 (Real.log cϱ) := le_max_left _ _
  have hlogbound : Real.log (cϱ * p.L / (4 * p.w)) ≤ max 0 (Real.log cϱ) + Real.log p.L := by
    calc Real.log (cϱ * p.L / (4 * p.w)) ≤ Real.log (cϱ * p.L) := by
          apply Real.log_le_log (by positivity)
          apply div_le_self (by positivity)
          linarith
      _ = Real.log cϱ + Real.log p.L := Real.log_mul (by positivity) (by positivity)
      _ ≤ max 0 (Real.log cϱ) + Real.log p.L := by
          have := le_max_right (0 : ℝ) (Real.log cϱ)
          linarith
  have hA : ∫ x, F.Phi x ^ 2 * |x| ≤ (12 + 4 * max 0 (Real.log cϱ)) * Real.log p.L := by
    refine hI1.trans ?_
    have h8 : 8 + 8 * Real.log (cϱ * p.L / (4 * p.w))
        ≤ 8 + 8 * (max 0 (Real.log cϱ) + Real.log p.L) := by linarith
    refine h8.trans ?_
    nlinarith [mul_nonneg hm0 (by linarith : (0 : ℝ) ≤ Real.log p.L - 2)]
  have hB : ∫ x, F.Phi x ^ 2 * x ^ 2 ≤ 8 + 2 * cϱ ^ 2 := by
    refine hI2.trans ?_
    have hdiv : cϱ / p.w ≤ cϱ := div_le_self (by linarith) hw1
    have hdivnn : 0 ≤ cϱ / p.w := by positivity
    nlinarith
  have hI1nn : 0 ≤ ∫ x, F.Phi x ^ 2 * |x| := integral_nonneg fun x => by positivity
  have hI2nn : 0 ≤ ∫ x, F.Phi x ^ 2 * x ^ 2 := integral_nonneg fun x => by positivity
  refine hcore.trans ?_
  have hstep : (1 + K) * p.l ^ 2 * (∫ x, F.Phi x ^ 2 * |x|)
        + 10 * p.l * ∫ x, F.Phi x ^ 2 * x ^ 2
      ≤ (1 + K) * p.l ^ 2 * ((12 + 4 * max 0 (Real.log cϱ)) * Real.log p.L)
        + 10 * p.l * (8 + 2 * cϱ ^ 2) := by
    gcongr
  refine hstep.trans ?_
  have hlt : (0 : ℝ) ≤ p.l * Real.log p.L - 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ p.l - 1) (by linarith : (0 : ℝ) ≤ Real.log p.L)]
  have h82 : (0 : ℝ) ≤ 8 + 2 * cϱ ^ 2 := by positivity
  have hfin : 10 * p.l * (8 + 2 * cϱ ^ 2)
      ≤ 5 * (8 + 2 * cϱ ^ 2) * (p.l ^ 2 * Real.log p.L) := by
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ p.l) h82) hlt]
  nlinarith [hfin]

end PrimeSide
end Zeta23
