/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmE/MuMuChi.lean — [prop:mumu] for Dirichlet characters (Theorem E, paper sec 7.2):
the diagonal mu_chi-evaluation.

Differences from the zeta-version: mu -> muq kappa q; window sup-bound |mu_chi| <= C_a * l
(muq_abs_le) instead of |mu| <= l, so the core lemmas carry an abstract bound A (>= 0); the
K-increment arrives in unified K(|r|+r^2)/t shape (muq_increment_bound); constants fold at the
end (C is existentially bound).
-/
import Zeta23.ThmE.PrimeSideChi
import Zeta23.PrimeSideB.PPKernel

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Real Set
open scoped BigOperators

namespace Zeta23
namespace ThmE

open Zeta23.PrimeSide

variable {cϱ : ℝ} {κ : ℕ} {q : ℕ}

section Core

variable {p : Setting} {F : LocalFun}

/-- Core scalar estimate (chi-version): for every x, the inner shear integral differs from
the window integral of muq^2 by at most (A^2 + A*K)|x| + A*K*x^2. -/
theorem abs_inner_sub_le_chi (hΓq : GammaFactsChi κ q) (hT2 : 2 ≤ p.T)
    {A : ℝ} (hA0 : 0 ≤ A)
    (hμl : ∀ τ ∈ Icc p.T (2 * p.T), |muq κ q τ| ≤ A)
    {K : ℝ} (hK0 : 0 ≤ K)
    (hKinc : ∀ t : ℝ, 2 ≤ t → ∀ r : ℝ,
      |muq κ q (t + r) - muq κ q t| ≤ K * (|r| + r ^ 2) / t)
    (x : ℝ) :
    |(∫ τ' in Ix p.T x, muq κ q (x + τ') * muq κ q τ')
        - ∫ τ' in Icc p.T (2 * p.T), muq κ q τ' ^ 2|
      ≤ (A ^ 2 + A * K) * |x| + A * K * x ^ 2 := by
  have hμc : Continuous (muq κ q) := hΓq.smooth.continuous
  have hT0 : (0 : ℝ) < p.T := by linarith
  have hcnn : 0 ≤ ∫ τ' in Icc p.T (2 * p.T), muq κ q τ' ^ 2 :=
    setIntegral_nonneg measurableSet_Icc fun τ' _ => sq_nonneg _
  have hsq_bound : ∀ τ' ∈ Icc p.T (2 * p.T), ‖muq κ q τ' ^ 2‖ ≤ A ^ 2 := by
    intro τ' hτ'
    have h := hμl τ' hτ'
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [abs_nonneg (muq κ q τ'), sq_abs (muq κ q τ')]
  have hcle : ∫ τ' in Icc p.T (2 * p.T), muq κ q τ' ^ 2 ≤ A ^ 2 * p.T := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc p.T (2 * p.T))
      (f := fun τ' => muq κ q τ' ^ 2)
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top) hsq_bound
    rw [Real.norm_eq_abs, abs_of_nonneg hcnn, measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith), show 2 * p.T - p.T = p.T by ring] at h
    exact h
  rcases le_or_gt |x| p.T with hx | hx
  · have hIle : max (p.T - x) p.T ≤ min (2 * p.T - x) (2 * p.T) := Ix_le hT0.le hx
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
    have hIxInt1 : IntegrableOn (fun τ' => muq κ q (x + τ') * muq κ q τ') (Ix p.T x) :=
      ContinuousOn.integrableOn_compact hIxcompact (by fun_prop)
    have hIxInt2 : IntegrableOn (fun τ' => muq κ q τ' ^ 2) (Ix p.T x) :=
      ContinuousOn.integrableOn_compact hIxcompact (by fun_prop)
    have hIInt2 : IntegrableOn (fun τ' => muq κ q τ' ^ 2) (Icc p.T (2 * p.T)) :=
      ContinuousOn.integrableOn_compact isCompact_Icc (by fun_prop)
    have hlip : |(∫ τ' in Ix p.T x, muq κ q (x + τ') * muq κ q τ')
        - ∫ τ' in Ix p.T x, muq κ q τ' ^ 2| ≤ A * (K * (|x| + x ^ 2)) := by
      rw [← integral_sub hIxInt1 hIxInt2]
      have hb : ∀ τ' ∈ Ix p.T x,
          ‖muq κ q (x + τ') * muq κ q τ' - muq κ q τ' ^ 2‖
            ≤ K * (|x| + x ^ 2) / p.T * A := by
        intro τ' hτ'
        obtain ⟨_, hmem2⟩ := mem_Ix.mp hτ'
        have hτT : p.T ≤ τ' := hmem2.1
        have h2τ : 2 ≤ τ' := by linarith
        have hinc := hKinc τ' h2τ x
        rw [show τ' + x = x + τ' by ring] at hinc
        have hμτ : |muq κ q τ'| ≤ A := hμl τ' hmem2
        have hqd : K * (|x| + x ^ 2) / τ' ≤ K * (|x| + x ^ 2) / p.T := by
          gcongr
        calc ‖muq κ q (x + τ') * muq κ q τ' - muq κ q τ' ^ 2‖
            = |muq κ q (x + τ') - muq κ q τ'| * |muq κ q τ'| := by
              rw [Real.norm_eq_abs, ← abs_mul]; congr 1; ring
          _ ≤ K * (|x| + x ^ 2) / p.T * A :=
              mul_le_mul (hinc.trans hqd) hμτ (abs_nonneg _) (by positivity)
      have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ix p.T x)
        (f := fun τ' => muq κ q (x + τ') * muq κ q τ' - muq κ q τ' ^ 2)
        (lt_of_le_of_ne (le_top) hIxfin) hb
      rw [Real.norm_eq_abs, hIxvol] at h
      refine h.trans ?_
      have hfrac : (p.T - |x|) / p.T ≤ 1 := by
        rw [div_le_one hT0]; linarith [abs_nonneg x]
      have hnum : (0 : ℝ) ≤ K * (|x| + x ^ 2) := by positivity
      calc K * (|x| + x ^ 2) / p.T * A * (p.T - |x|)
          = A * (K * (|x| + x ^ 2)) * ((p.T - |x|) / p.T) := by ring
        _ ≤ A * (K * (|x| + x ^ 2)) * 1 := by
            have : (0 : ℝ) ≤ A * (K * (|x| + x ^ 2)) := by positivity
            exact mul_le_mul_of_nonneg_left hfrac this
        _ = A * (K * (|x| + x ^ 2)) := mul_one _
    have hcomp : |(∫ τ' in Ix p.T x, muq κ q τ' ^ 2)
        - ∫ τ' in Icc p.T (2 * p.T), muq κ q τ' ^ 2| ≤ A ^ 2 * |x| := by
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
      have hb : ∀ τ' ∈ Icc p.T (2 * p.T) \ Ix p.T x, ‖muq κ q τ' ^ 2‖ ≤ A ^ 2 :=
        fun τ' hτ' => hsq_bound τ' hτ'.1
      have h := norm_setIntegral_le_of_norm_le_const (μ := volume)
        (s := Icc p.T (2 * p.T) \ Ix p.T x) (f := fun τ' => muq κ q τ' ^ 2)
        (lt_of_le_of_lt (measure_mono Set.sdiff_subset)
          (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)) hb
      rw [Real.norm_eq_abs, hdvol] at h
      exact h
    refine (abs_sub_le _ (∫ τ' in Ix p.T x, muq κ q τ' ^ 2) _).trans ?_
    refine (add_le_add hlip hcomp).trans ?_
    nlinarith [abs_nonneg x, sq_nonneg x, mul_nonneg (mul_nonneg hA0 hK0) (abs_nonneg x)]
  · rw [Ix_eq_empty hT0.le hx, Measure.restrict_empty, integral_zero_measure, zero_sub,
      abs_neg, abs_of_nonneg hcnn]
    refine hcle.trans ?_
    nlinarith [mul_nonneg (sq_nonneg A) (by linarith : (0 : ℝ) ≤ |x| - p.T),
      mul_nonneg (mul_nonneg hA0 hK0) (abs_nonneg x),
      mul_nonneg (mul_nonneg hA0 hK0) (sq_nonneg x)]

/-- Core estimate of [prop:mumu]_chi at fixed (p, F). -/
theorem mumu_core_chi (hΓq : GammaFactsChi κ q) (hF : LocalHypsCore cϱ p F) (hT2 : 2 ≤ p.T)
    {A : ℝ} (hA0 : 0 ≤ A)
    (hμl : ∀ τ ∈ Icc p.T (2 * p.T), |muq κ q τ| ≤ A)
    {K : ℝ} (hK0 : 0 ≤ K)
    (hKinc : ∀ t : ℝ, 2 ≤ t → ∀ r : ℝ,
      |muq κ q (t + r) - muq κ q t| ≤ K * (|r| + r ^ 2) / t) :
    |Mform F.Phi p.T (muq κ q) (muq κ q)
        - 2 * π * F.b * p.L * ∫ τ in p.T..(2 * p.T), muq κ q τ ^ 2|
      ≤ (A ^ 2 + A * K) * (∫ x, F.Phi x ^ 2 * |x|)
        + A * K * ∫ x, F.Phi x ^ 2 * x ^ 2 := by
  have hμc : Continuous (muq κ q) := hΓq.smooth.continuous
  have hΦc : Continuous F.Phi := hF.Phi_contDiff.continuous
  have hGc : Continuous fun qq : ℝ × ℝ => muq κ q qq.1 * muq κ q qq.2 := by fun_prop
  set c : ℝ := ∫ τ' in Icc p.T (2 * p.T), muq κ q τ' ^ 2 with hc
  have hc' : ∫ τ in p.T..(2 * p.T), muq κ q τ ^ 2 = c := by
    rw [intervalIntegral.integral_of_le (by linarith), hc, integral_Icc_eq_integral_Ioc]
  have hshear : Mform F.Phi p.T (muq κ q) (muq κ q)
      = ∫ x, F.Phi x ^ 2 * ∫ τ' in Ix p.T x, muq κ q (x + τ') * muq κ q τ' := by
    unfold Mform
    simp only [mul_assoc]
    exact sqIntegral_shear hΦc hGc
  have hfInt : Integrable (fun x => F.Phi x ^ 2 * ∫ τ' in Ix p.T x,
      muq κ q (x + τ') * muq κ q τ') := integrable_sq_mul_inner hΦc hGc
  have hgInt : Integrable (fun x => F.Phi x ^ 2 * c) := hF.Phi_sq_integrable.mul_const c
  have hmain : 2 * π * F.b * p.L * c = ∫ x, F.Phi x ^ 2 * c := by
    rw [integral_mul_const c (fun x => F.Phi x ^ 2), hF.Phi_sq_integral]
  rw [hc', hshear, hmain, ← integral_sub hfInt hgInt]
  have hpt : ∀ x : ℝ, |F.Phi x ^ 2 * (∫ τ' in Ix p.T x, muq κ q (x + τ') * muq κ q τ')
      - F.Phi x ^ 2 * c|
      ≤ (A ^ 2 + A * K) * (F.Phi x ^ 2 * |x|) + A * K * (F.Phi x ^ 2 * x ^ 2) := by
    intro x
    rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg (F.Phi x))]
    have hinner := abs_inner_sub_le_chi hΓq hT2 hA0 hμl hK0 hKinc x
    rw [← hc] at hinner
    calc F.Phi x ^ 2 * |(∫ τ' in Ix p.T x, muq κ q (x + τ') * muq κ q τ') - c|
        ≤ F.Phi x ^ 2 * ((A ^ 2 + A * K) * |x| + A * K * x ^ 2) := by
          gcongr
      _ = (A ^ 2 + A * K) * (F.Phi x ^ 2 * |x|) + A * K * (F.Phi x ^ 2 * x ^ 2) := by ring
  calc |∫ x, (F.Phi x ^ 2 * (∫ τ' in Ix p.T x, muq κ q (x + τ') * muq κ q τ')
        - F.Phi x ^ 2 * c)|
      ≤ ∫ x, |F.Phi x ^ 2 * (∫ τ' in Ix p.T x, muq κ q (x + τ') * muq κ q τ')
        - F.Phi x ^ 2 * c| := by
        rw [← Real.norm_eq_abs]
        refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
        simp_rw [Real.norm_eq_abs]
    _ ≤ ∫ x, ((A ^ 2 + A * K) * (F.Phi x ^ 2 * |x|) + A * K * (F.Phi x ^ 2 * x ^ 2)) :=
        integral_mono (hfInt.sub hgInt).abs
          ((hF.Phi_sq_mul_abs_integrable.const_mul _).add
            (hF.Phi_sq_mul_sq_integrable.const_mul _)) hpt
    _ = (A ^ 2 + A * K) * (∫ x, F.Phi x ^ 2 * |x|)
        + A * K * ∫ x, F.Phi x ^ 2 * x ^ 2 := by
        rw [integral_add (hF.Phi_sq_mul_abs_integrable.const_mul _)
          (hF.Phi_sq_mul_sq_integrable.const_mul _),
          integral_const_mul, integral_const_mul]

end Core

variable (cϱ lam : ℝ)

set_option linter.unusedVariables false in
set_option maxHeartbeats 1000000 in
/-- [prop:mumu]_chi: the diagonal mu_chi evaluation with O_q(l^2 log L) error; proof of the
statement recorded in Zeta23/ThmE/PrimeSideChi.lean. -/
theorem prop_mumu_chi {κ q : ℕ} {c : ℕ → ℂ} (hΓq : GammaFactsChi κ q) (hc : CoeffOK q c)
    (hq : 1 ≤ q) (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAtCore cϱ lam (fun p F =>
      |Mform F.Phi p.T (muq κ q) (muq κ q)
          - 2 * π * F.b * p.L * ∫ τ in p.T..(2 * p.T), muq κ q τ ^ 2|
        ≤ C * (Zeta23.l p.T ^ 2 * Real.log p.L)) := by
  obtain ⟨K, hK0, hKinc⟩ := muq_increment_bound hΓq hq
  obtain ⟨Ca, T₀a, hCa0, hT₀a⟩ := muq_abs_le κ q hΓq hq
  refine ⟨(Ca ^ 2 + Ca * K) * (12 + 4 * max 0 (Real.log cϱ))
      + (Ca ^ 2 + Ca * K) * (8 + 2 * cϱ ^ 2),
    max T₀a 2, fun p F hplam hT hF => ?_⟩
  have hT2 : 2 ≤ p.T := le_trans (le_max_right _ _) hT
  have hμl := hT₀a p (le_trans (le_max_left _ _) hT)
  have hl1 : 1 ≤ p.l := hF.one_le_l
  have hl0 : (0 : ℝ) ≤ p.l := by linarith
  have hA0 : (0 : ℝ) ≤ Ca * p.l := by positivity
  have hcore := mumu_core_chi hΓq hF hT2 hA0 hμl hK0 hKinc
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
  have hm0 : 0 ≤ max 0 (Real.log cϱ) := le_max_left _ _
  have hA : ∫ x, F.Phi x ^ 2 * |x| ≤ (12 + 4 * max 0 (Real.log cϱ)) * Real.log p.L := by
    refine hI1.trans ?_
    have hlogbound : Real.log (cϱ * p.L / (4 * p.w)) ≤ max 0 (Real.log cϱ) + Real.log p.L := by
      calc Real.log (cϱ * p.L / (4 * p.w)) ≤ Real.log (cϱ * p.L) := by
            apply Real.log_le_log (by positivity)
            apply div_le_self (by positivity)
            linarith
        _ = Real.log cϱ + Real.log p.L := Real.log_mul (by positivity) (by positivity)
        _ ≤ max 0 (Real.log cϱ) + Real.log p.L := by
            have := le_max_right (0 : ℝ) (Real.log cϱ)
            linarith
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
  have hAK0 : (0 : ℝ) ≤ (Ca * p.l) ^ 2 + (Ca * p.l) * K := by positivity
  have hstep : ((Ca * p.l) ^ 2 + (Ca * p.l) * K) * (∫ x, F.Phi x ^ 2 * |x|)
        + (Ca * p.l) * K * (∫ x, F.Phi x ^ 2 * x ^ 2)
      ≤ ((Ca * p.l) ^ 2 + (Ca * p.l) * K) * ((12 + 4 * max 0 (Real.log cϱ)) * Real.log p.L)
        + ((Ca * p.l) ^ 2 + (Ca * p.l) * K) * (8 + 2 * cϱ ^ 2) := by
    have h1 : ((Ca * p.l) ^ 2 + (Ca * p.l) * K) * (∫ x, F.Phi x ^ 2 * |x|)
        ≤ ((Ca * p.l) ^ 2 + (Ca * p.l) * K) * ((12 + 4 * max 0 (Real.log cϱ)) * Real.log p.L) :=
      mul_le_mul_of_nonneg_left hA hAK0
    have h2 : (Ca * p.l) * K * (∫ x, F.Phi x ^ 2 * x ^ 2)
        ≤ ((Ca * p.l) ^ 2 + (Ca * p.l) * K) * (8 + 2 * cϱ ^ 2) := by
      have h3 : (Ca * p.l) * K * (∫ x, F.Phi x ^ 2 * x ^ 2)
          ≤ (Ca * p.l) * K * (8 + 2 * cϱ ^ 2) :=
        mul_le_mul_of_nonneg_left hB (by positivity)
      refine h3.trans ?_
      have : (0 : ℝ) ≤ (Ca * p.l) ^ 2 := sq_nonneg _
      nlinarith [sq_nonneg (Ca * p.l), mul_nonneg (by positivity : (0:ℝ) ≤ 8 + 2 * cϱ ^ 2)
        (sq_nonneg (Ca * p.l))]
    linarith
  refine hstep.trans ?_
  -- fold into C * (l^2 log L), using l >= 1, log L >= 2, and l = Zeta23.l p.T
  have hleq : p.l = Zeta23.l p.T := rfl
  have hl2 : (1 : ℝ) ≤ p.l ^ 2 := by nlinarith
  have hKCa : (0:ℝ) ≤ Ca * K := by positivity
  have hCK : ((Ca * p.l) ^ 2 + (Ca * p.l) * K)
      ≤ (Ca ^ 2 + Ca * K) * p.l ^ 2 := by
    have : (Ca * p.l) * K ≤ Ca * K * p.l ^ 2 := by
      nlinarith [mul_nonneg hKCa (by nlinarith : (0:ℝ) ≤ p.l ^ 2 - p.l)]
    nlinarith [sq_nonneg (Ca * p.l)]
  have hCK0 : (0:ℝ) ≤ Ca ^ 2 + Ca * K := by positivity
  have h12m : (0 : ℝ) ≤ 12 + 4 * max 0 (Real.log cϱ) := by positivity
  have h82 : (0 : ℝ) ≤ 8 + 2 * cϱ ^ 2 := by positivity
  rw [← hleq]
  calc ((Ca * p.l) ^ 2 + (Ca * p.l) * K) * ((12 + 4 * max 0 (Real.log cϱ)) * Real.log p.L)
        + ((Ca * p.l) ^ 2 + (Ca * p.l) * K) * (8 + 2 * cϱ ^ 2)
      ≤ (Ca ^ 2 + Ca * K) * p.l ^ 2 * ((12 + 4 * max 0 (Real.log cϱ)) * Real.log p.L)
        + (Ca ^ 2 + Ca * K) * p.l ^ 2 * ((8 + 2 * cϱ ^ 2) * Real.log p.L) := by
        have ha := mul_le_mul_of_nonneg_right hCK
          (by positivity : (0:ℝ) ≤ (12 + 4 * max 0 (Real.log cϱ)) * Real.log p.L)
        have hb2 : ((Ca * p.l) ^ 2 + (Ca * p.l) * K) * (8 + 2 * cϱ ^ 2)
            ≤ (Ca ^ 2 + Ca * K) * p.l ^ 2 * ((8 + 2 * cϱ ^ 2) * Real.log p.L) := by
          have h1 := mul_le_mul_of_nonneg_right hCK h82
          refine h1.trans ?_
          have h2 : (1:ℝ) ≤ Real.log p.L := by linarith
          calc (Ca ^ 2 + Ca * K) * p.l ^ 2 * (8 + 2 * cϱ ^ 2)
              ≤ (Ca ^ 2 + Ca * K) * p.l ^ 2 * (8 + 2 * cϱ ^ 2) * Real.log p.L :=
                le_mul_of_one_le_right (by positivity) h2
            _ = (Ca ^ 2 + Ca * K) * p.l ^ 2 * ((8 + 2 * cϱ ^ 2) * Real.log p.L) := by ring
        linarith
    _ = ((Ca ^ 2 + Ca * K) * (12 + 4 * max 0 (Real.log cϱ))
          + (Ca ^ 2 + Ca * K) * (8 + 2 * cϱ ^ 2)) * (p.l ^ 2 * Real.log p.L) := by
        ring

end ThmE
end Zeta23
