/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/QuarticWindow/Moments.lean — the moments of the quartic window vs their scale-free limits
(consumed by the J_T limit in Zeta23/XiPrime/Window.lean).

With φ_Q := P.phiV vQuartic T (= phiM (fQ L) φ), φ_Q² = v(u/L)·φ(u)² on the core and φ differs from the sharp
cutoff 1_{[−L/2,L/2]} only on the two ramps of width w (the generic edge estimate of Zeta23/ThmD/Window.lean,
copied here since it is private there):
  aV_quartic_close :  |a_V − ∫v|  = |L⁻¹∫φ_Q² − 2777/3000|     ≤ 2w/L,
  bV_quartic_close :  |b_V − ∫v²| = |L⁻¹∫φ_Q⁴ − 518783/600000| ≤ 2w/L,
  gV_quartic_close :  |g_{φ_Q}(y) − L·vConv vQuartic (y/L)| ≤ 4w  for y ∈ [0, L]  (g = φ_Q² ⋆ φ_Q²),
hence b_V ≥ 1/2 (already at 8w ≤ L) and the eventual §5 LocalHypsCore for the quartic data
(localHypsCoreQ_eventually).
-/
import Zeta23.XiPrime.QuarticWindow.Quartic
import Zeta23.ThmD.WindowLocalHyps
import Zeta23.PrimeSideB.Concrete

noncomputable section

open Real Set MeasureTheory Filter Topology

namespace Zeta23
namespace XiPrime

variable {ϱ : ℝ → ℝ} {L w : ℝ}

/-! ### generic edge estimate and scaling -/

theorem edge_estimate {h p : ℝ → ℝ} {L w : ℝ} (_hL : 0 < L) (hw0 : 0 < w)
    (hwL : 2 * w ≤ L) (hh : ∀ u, |h u| ≤ 1) (hp0 : ∀ u, 0 ≤ p u) (hp1 : ∀ u, p u ≤ 1)
    (hpl : ∀ u : ℝ, |u| ≤ L/2 - w → p u = 1) (hsupp : ∀ u : ℝ, L/2 ≤ |u| → p u = 0)
    (hpc : Continuous p) (hhc : Continuous h) :
    |(∫ u, h u * p u) - ∫ u in Set.Icc (-(L/2)) (L/2), h u| ≤ 2 * w := by
  have hrestr : ∫ u, h u * p u = ∫ u in Set.Icc (-(L/2)) (L/2), h u * p u := by
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    have : L / 2 ≤ |x| := by
      rcases hx with hc | hc
      · rw [abs_of_neg (by linarith : x < 0)]; linarith
      · rw [abs_of_pos (by linarith : 0 < x)]; linarith
    rw [hsupp x this, mul_zero]
  have hIhp : MeasureTheory.IntegrableOn (fun u => h u * p u) (Set.Icc (-(L/2)) (L/2)) :=
    ((hhc.mul hpc).continuousOn).integrableOn_compact isCompact_Icc
  have hIh : MeasureTheory.IntegrableOn h (Set.Icc (-(L/2)) (L/2)) :=
    (hhc.continuousOn).integrableOn_compact isCompact_Icc
  have hsub : (∫ u, h u * p u) - ∫ u in Set.Icc (-(L/2)) (L/2), h u
      = ∫ u in Set.Icc (-(L/2)) (L/2), (h u * p u - h u) := by
    rw [hrestr, ← MeasureTheory.integral_sub hIhp hIh]
  rw [hsub]
  set maj : ℝ → ℝ := fun u => (Set.Icc (-(L/2)) (-(L/2) + w)).indicator (1 : ℝ → ℝ) u
      + (Set.Icc (L/2 - w) (L/2)).indicator (1 : ℝ → ℝ) u with hmaj
  have hImaj : Integrable maj := by
    apply Integrable.add
    · exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
        (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
    · exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
        (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  have hind0 : ∀ (s : Set ℝ) (u : ℝ), 0 ≤ s.indicator (1 : ℝ → ℝ) u := fun s u =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) u
  have hptw : ∀ u ∈ Set.Icc (-(L/2)) (L/2), |h u * p u - h u| ≤ maj u := by
    intro u hu
    have hmaj0 : 0 ≤ maj u := by
      rw [hmaj]
      exact add_nonneg (hind0 _ u) (hind0 _ u)
    rcases le_or_gt |u| (L/2 - w) with hpl' | hedge
    · rw [hpl u hpl', mul_one, sub_self, abs_zero]
      exact hmaj0
    · have hbound : |h u * p u - h u| ≤ 1 := by
        have e : h u * p u - h u = h u * (p u - 1) := by ring
        rw [e, abs_mul]
        calc |h u| * |p u - 1| ≤ 1 * 1 := by
              apply mul_le_mul (hh u) ?_ (abs_nonneg _) zero_le_one
              rw [abs_le]
              exact ⟨by linarith [hp0 u], by linarith [hp1 u]⟩
          _ = 1 := mul_one 1
      have hone : (1:ℝ) ≤ maj u := by
        rw [hmaj]
        show (1:ℝ) ≤ (Set.Icc (-(L/2)) (-(L/2) + w)).indicator (1 : ℝ → ℝ) u
          + (Set.Icc (L/2 - w) (L/2)).indicator (1 : ℝ → ℝ) u
        rcases le_or_gt u 0 with hneg | hpos
        · have hu1 : u ∈ Set.Icc (-(L/2)) (-(L/2) + w) := by
            refine ⟨hu.1, ?_⟩
            have habs : |u| = -u := abs_of_nonpos hneg
            rw [habs] at hedge
            linarith
          have := hind0 (Set.Icc (L/2 - w) (L/2)) u
          rw [Set.indicator_of_mem hu1, Pi.one_apply]
          linarith
        · have hu1 : u ∈ Set.Icc (L/2 - w) (L/2) := by
            refine ⟨?_, hu.2⟩
            have habs : |u| = u := abs_of_pos hpos
            rw [habs] at hedge
            linarith
          have := hind0 (Set.Icc (-(L/2)) (-(L/2) + w)) u
          rw [Set.indicator_of_mem hu1, Pi.one_apply]
          linarith
      linarith
  calc |∫ u in Set.Icc (-(L/2)) (L/2), (h u * p u - h u)|
      ≤ ∫ u in Set.Icc (-(L/2)) (L/2), |h u * p u - h u| :=
        MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ u in Set.Icc (-(L/2)) (L/2), maj u := by
        apply MeasureTheory.setIntegral_mono_on
          (((hhc.mul hpc).sub hhc).abs.continuousOn.integrableOn_compact isCompact_Icc)
          hImaj.integrableOn measurableSet_Icc hptw
    _ ≤ ∫ u, maj u :=
        MeasureTheory.setIntegral_le_integral hImaj
          (MeasureTheory.ae_of_all _ fun u => by
            rw [hmaj]
            apply add_nonneg <;> exact Set.indicator_nonneg (fun _ _ => zero_le_one) u)
    _ = 2 * w := by
        rw [hmaj]
        rw [MeasureTheory.integral_add
          ((MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
            (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)))
          ((MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
            (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)))]
        rw [MeasureTheory.integral_indicator_one measurableSet_Icc,
          MeasureTheory.integral_indicator_one measurableSet_Icc,
          MeasureTheory.measureReal_def, MeasureTheory.measureReal_def,
          Real.volume_Icc, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
        ring

/-- substitution: ∫_{−L/2..L/2} g(u/L) du = L · ∫_{−1/2..1/2} g. -/
theorem integral_scale {g : ℝ → ℝ} {L : ℝ} (hL : 0 < L) :
    ∫ u in (-(L/2))..(L/2), g (u / L) = L * ∫ s in (-(1:ℝ)/2)..(1/2), g s := by
  rw [intervalIntegral.integral_comp_div (f := g) hL.ne', smul_eq_mul,
    show -(L/2) / L = -(1:ℝ)/2 by field_simp; try ring,
    show L/2 / L = (1:ℝ)/2 by rw [div_div]; rw [div_eq_div_iff (by positivity) (by norm_num)]; ring]

/-! ### φ_Q² and the profile -/

/-- the squared modulating factor, globally: m u := max 0 (v(u/L)) = f_Q² ∈ [0,1]. -/
def mQ (L : ℝ) (u : ℝ) : ℝ := max 0 (vQuartic (u / L))

lemma mQ_nonneg (u : ℝ) : 0 ≤ mQ L u := le_max_left _ _
lemma mQ_le_one (u : ℝ) : mQ L u ≤ 1 := max_le zero_le_one (vQuartic_le_one _)
lemma abs_mQ_le_one (u : ℝ) : |mQ L u| ≤ 1 := by rw [abs_of_nonneg (mQ_nonneg u)]; exact mQ_le_one u
lemma mQ_continuous (_hL : 0 < L) : Continuous (mQ L) := by
  unfold mQ; exact continuous_const.max (continuous_vQuartic.comp (continuous_id.div_const L))
lemma fQ_sq (u : ℝ) : fQ L u ^ 2 = mQ L u := Real.sq_sqrt (le_max_left _ _)
lemma mQ_core (hL : 0 < L) {u : ℝ} (hu : u ∈ Icc (-(L/2)) (L/2)) : mQ L u = vQuartic (u / L) :=
  max_eq_right (vQuartic_pos (core_mem hL (abs_le.mpr ⟨hu.1, hu.2⟩))).le

lemma phiMQ_sq_eq (u : ℝ) : phiM (fQ L) ϱ L w u ^ 2 = mQ L u * Taper.phi ϱ L w u ^ 2 := by
  rw [phiM, mul_pow, fQ_sq]

lemma phiMQ_pow_four_eq (u : ℝ) : phiM (fQ L) ϱ L w u ^ 4 = mQ L u ^ 2 * Taper.phi ϱ L w u ^ 4 := by
  have : phiM (fQ L) ϱ L w u ^ 4 = (phiM (fQ L) ϱ L w u ^ 2) ^ 2 := by ring
  rw [this, phiMQ_sq_eq]; ring

/-! ### a and b -/

/-- |L⁻¹∫φ_Q² − ∫v| ≤ 2w/L. -/
theorem aQ_close (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    |L⁻¹ * (∫ u, phiM (fQ L) ϱ L w u ^ 2) - 2777 / 3000| ≤ 2 * w / L := by
  have hw0 : 0 < w := by linarith
  have hwL' : 2 * w ≤ L := by linarith
  have hL : 0 < L := by linarith
  have hsub : (2777 : ℝ) / 3000 = L⁻¹ * ∫ u in Set.Icc (-(L/2)) (L/2), mQ L u := by
    rw [setIntegral_congr_fun measurableSet_Icc (fun u hu => mQ_core hL hu),
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -(L/2) ≤ L/2), integral_scale hL,
      integral_vQuartic]
    field_simp
  have hwin : ∫ u, phiM (fQ L) ϱ L w u ^ 2 = ∫ u, mQ L u * Taper.phi ϱ L w u ^ 2 :=
    integral_congr_ae (ae_of_all _ fun u => phiMQ_sq_eq u)
  rw [hwin, hsub]
  have hcore := edge_estimate (h := mQ L) (p := fun u => Taper.phi ϱ L w u ^ 2) hL hw0 hwL'
    abs_mQ_le_one (fun u => sq_nonneg _)
    (fun u => by
      calc Taper.phi ϱ L w u ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (Taper.phi_nonneg hϱ u) (Taper.phi_le_one hϱ u) 2
        _ = 1 := one_pow 2)
    (fun u hu => by show Taper.phi ϱ L w u ^ 2 = 1; rw [Taper.phi_eq_one hϱ hw0 hu, one_pow])
    (fun u hu => by show Taper.phi ϱ L w u ^ 2 = 0; rw [Taper.phi_eq_zero hϱ hw0 hu, zero_pow two_ne_zero])
    ((Taper.phi_continuous hϱ hw0 hwL').pow 2) (mQ_continuous hL)
  have e : L⁻¹ * (∫ u, mQ L u * Taper.phi ϱ L w u ^ 2) - L⁻¹ * ∫ u in Set.Icc (-(L/2)) (L/2), mQ L u
      = L⁻¹ * ((∫ u, mQ L u * Taper.phi ϱ L w u ^ 2) - ∫ u in Set.Icc (-(L/2)) (L/2), mQ L u) := by ring
  rw [e, abs_mul, abs_of_pos (by positivity : (0:ℝ) < L⁻¹)]
  calc L⁻¹ * |(∫ u, mQ L u * Taper.phi ϱ L w u ^ 2) - ∫ u in Set.Icc (-(L/2)) (L/2), mQ L u|
      ≤ L⁻¹ * (2 * w) := mul_le_mul_of_nonneg_left hcore (by positivity)
    _ = 2 * w / L := by rw [div_eq_inv_mul]

/-- |L⁻¹∫φ_Q⁴ − ∫v²| ≤ 2w/L. -/
theorem bQ_close (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    |L⁻¹ * (∫ u, phiM (fQ L) ϱ L w u ^ 4) - 518783 / 600000| ≤ 2 * w / L := by
  have hw0 : 0 < w := by linarith
  have hwL' : 2 * w ≤ L := by linarith
  have hL : 0 < L := by linarith
  have hsub : (518783 : ℝ) / 600000 = L⁻¹ * ∫ u in Set.Icc (-(L/2)) (L/2), mQ L u ^ 2 := by
    rw [setIntegral_congr_fun measurableSet_Icc (fun u hu => by show mQ L u ^ 2 = vQuartic (u / L) ^ 2; rw [mQ_core hL hu]),
      MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : -(L/2) ≤ L/2),
      integral_scale (g := fun s => vQuartic s ^ 2) hL, integral_vQuartic_sq]
    field_simp
  have hwin : ∫ u, phiM (fQ L) ϱ L w u ^ 4 = ∫ u, mQ L u ^ 2 * Taper.phi ϱ L w u ^ 4 :=
    integral_congr_ae (ae_of_all _ fun u => phiMQ_pow_four_eq u)
  rw [hwin, hsub]
  have hcore := edge_estimate (h := fun u => mQ L u ^ 2) (p := fun u => Taper.phi ϱ L w u ^ 4) hL hw0 hwL'
    (fun u => by
      rw [abs_of_nonneg (sq_nonneg _)]
      calc mQ L u ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (mQ_nonneg u) (mQ_le_one u) 2
        _ = 1 := one_pow 2)
    (fun u => by positivity)
    (fun u => by
      calc Taper.phi ϱ L w u ^ 4 ≤ 1 ^ 4 := pow_le_pow_left₀ (Taper.phi_nonneg hϱ u) (Taper.phi_le_one hϱ u) 4
        _ = 1 := one_pow 4)
    (fun u hu => by show Taper.phi ϱ L w u ^ 4 = 1; rw [Taper.phi_eq_one hϱ hw0 hu, one_pow])
    (fun u hu => by show Taper.phi ϱ L w u ^ 4 = 0; rw [Taper.phi_eq_zero hϱ hw0 hu]; norm_num)
    ((Taper.phi_continuous hϱ hw0 hwL').pow 4) ((mQ_continuous hL).pow 2)
  have e : L⁻¹ * (∫ u, mQ L u ^ 2 * Taper.phi ϱ L w u ^ 4) - L⁻¹ * ∫ u in Set.Icc (-(L/2)) (L/2), mQ L u ^ 2
      = L⁻¹ * ((∫ u, mQ L u ^ 2 * Taper.phi ϱ L w u ^ 4) - ∫ u in Set.Icc (-(L/2)) (L/2), mQ L u ^ 2) := by
    ring
  rw [e, abs_mul, abs_of_pos (by positivity : (0:ℝ) < L⁻¹)]
  calc L⁻¹ * |(∫ u, mQ L u ^ 2 * Taper.phi ϱ L w u ^ 4) - ∫ u in Set.Icc (-(L/2)) (L/2), mQ L u ^ 2|
      ≤ L⁻¹ * (2 * w) := mul_le_mul_of_nonneg_left hcore (by positivity)
    _ = 2 * w / L := by rw [div_eq_inv_mul]

/-! ### the autocorrelation vs the sharp one -/

/-- the sharp window 1_{[−L/2,L/2]}·v(·/L). -/
def sharpQ (L : ℝ) (u : ℝ) : ℝ := (Set.Icc (-(L/2)) (L/2)).indicator (fun u => vQuartic (u / L)) u

theorem sharpQ_autocorr_eq (hL : 0 < L) {y : ℝ} (hy0 : 0 ≤ y) (hyL : y ≤ L) :
    ∫ u, sharpQ L u * sharpQ L (u + y) = L * vConv vQuartic (y / L) := by
  have hind : ∀ u : ℝ, sharpQ L u * sharpQ L (u + y)
      = (Set.Icc (-(L/2)) (L/2 - y)).indicator
          (fun u => vQuartic (u / L) * vQuartic ((u + y) / L)) u := by
    intro u
    unfold sharpQ
    by_cases hu : u ∈ Set.Icc (-(L/2)) (L/2 - y)
    · have hu1 : u ∈ Set.Icc (-(L/2)) (L/2) := ⟨hu.1, by linarith [hu.2]⟩
      have hu2 : u + y ∈ Set.Icc (-(L/2)) (L/2) := ⟨by linarith [hu.1], by linarith [hu.2]⟩
      rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu1, Set.indicator_of_mem hu2]
    · rw [Set.indicator_of_notMem hu]
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hu
      rcases hu with hu | hu
      · rw [Set.indicator_of_notMem (s := Set.Icc (-(L/2)) (L/2)) (a := u)
          (by rw [Set.mem_Icc]; push Not; intro h; linarith), zero_mul]
      · rw [Set.indicator_of_notMem (s := Set.Icc (-(L/2)) (L/2)) (a := u + y)
          (by rw [Set.mem_Icc]; push Not; intro h; linarith), mul_zero]
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hind),
    MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -(L/2) ≤ L/2 - y)]
  -- substitution u = L s
  have hsub := intervalIntegral.integral_comp_div (a := -(L/2)) (b := L/2 - y)
    (f := fun s => vQuartic s * vQuartic (s + y / L)) hL.ne'
  have e1 : -(L/2) / L = -(1:ℝ)/2 := by field_simp
  have e2 : (L/2 - y) / L = 1/2 - y / L := by field_simp
  rw [e1, e2, smul_eq_mul] at hsub
  unfold vConv
  rw [← hsub]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [add_div]

/-- ‖φ_Q² − sharp‖₁ ≤ 2w. -/
theorem integral_abs_phiMQsq_sub_sharp (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ∫ u, |phiM (fQ L) ϱ L w u ^ 2 - sharpQ L u| ≤ 2 * w := by
  have hL : 0 < L := by linarith
  set maj : ℝ → ℝ := fun u => (Set.Icc (-(L/2)) (-(L/2) + w)).indicator (1 : ℝ → ℝ) u
      + (Set.Icc (L/2 - w) (L/2)).indicator (1 : ℝ → ℝ) u with hmaj
  have hImaj : Integrable maj := by
    apply Integrable.add <;>
      exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
        (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  have hind0 : ∀ (s : Set ℝ) (u : ℝ), 0 ≤ s.indicator (1 : ℝ → ℝ) u := fun s u =>
    Set.indicator_nonneg (fun _ _ => zero_le_one) u
  have hpt : ∀ u : ℝ, |phiM (fQ L) ϱ L w u ^ 2 - sharpQ L u| ≤ maj u := by
    intro u
    have hmaj0 : 0 ≤ maj u := by
      rw [hmaj]
      exact add_nonneg (hind0 _ u) (hind0 _ u)
    have hval : phiM (fQ L) ϱ L w u ^ 2 = mQ L u * Taper.phi ϱ L w u ^ 2 := phiMQ_sq_eq u
    rcases le_or_gt |u| (L/2 - w) with hpl | hedge
    · have huIcc : u ∈ Set.Icc (-(L/2)) (L/2) := by
        rw [abs_le] at hpl
        constructor <;> [linarith [hpl.1]; linarith [hpl.2]]
      rw [hval, Taper.phi_eq_one hϱ hw hpl, one_pow, mul_one, mQ_core hL huIcc]
      unfold sharpQ
      rw [Set.indicator_of_mem huIcc, sub_self, abs_zero]
      exact hmaj0
    · rcases le_or_gt |u| (L/2) with hin | hout
      · have hbound : |phiM (fQ L) ϱ L w u ^ 2 - sharpQ L u| ≤ 1 := by
          have h1' : 0 ≤ phiM (fQ L) ϱ L w u ^ 2 := sq_nonneg _
          have h2' : phiM (fQ L) ϱ L w u ^ 2 ≤ 1 := by
            rw [hval]
            calc mQ L u * Taper.phi ϱ L w u ^ 2 ≤ 1 * 1 ^ 2 :=
                  mul_le_mul (mQ_le_one u)
                    (pow_le_pow_left₀ (Taper.phi_nonneg hϱ u) (Taper.phi_le_one hϱ u) 2)
                    (sq_nonneg _) zero_le_one
              _ = 1 := by norm_num
          have h3' : 0 ≤ sharpQ L u := by
            unfold sharpQ
            apply Set.indicator_nonneg
            intro x hx
            exact (vQuartic_pos (core_mem hL (abs_le.mpr ⟨hx.1, hx.2⟩))).le
          have h4' : sharpQ L u ≤ 1 := by
            unfold sharpQ
            by_cases hm : u ∈ Set.Icc (-(L/2)) (L/2)
            · rw [Set.indicator_of_mem hm]; exact vQuartic_le_one _
            · rw [Set.indicator_of_notMem hm]; exact zero_le_one
          rw [abs_le]
          constructor <;> linarith
        have hone : (1:ℝ) ≤ maj u := by
          rw [hmaj]
          show (1:ℝ) ≤ (Set.Icc (-(L/2)) (-(L/2) + w)).indicator (1 : ℝ → ℝ) u
            + (Set.Icc (L/2 - w) (L/2)).indicator (1 : ℝ → ℝ) u
          rcases le_or_gt u 0 with hneg | hpos
          · have hu1 : u ∈ Set.Icc (-(L/2)) (-(L/2) + w) := by
              refine ⟨?_, ?_⟩
              · have : |u| = -u := abs_of_nonpos hneg
                rw [this] at hin
                linarith
              · have : |u| = -u := abs_of_nonpos hneg
                rw [this] at hedge
                linarith
            have := hind0 (Set.Icc (L/2 - w) (L/2)) u
            rw [Set.indicator_of_mem hu1, Pi.one_apply]
            linarith
          · have hu1 : u ∈ Set.Icc (L/2 - w) (L/2) := by
              refine ⟨?_, ?_⟩
              · have : |u| = u := abs_of_pos hpos
                rw [this] at hedge
                linarith
              · have : |u| = u := abs_of_pos hpos
                rw [this] at hin
                linarith
            have := hind0 (Set.Icc (-(L/2)) (-(L/2) + w)) u
            rw [Set.indicator_of_mem hu1, Pi.one_apply]
            linarith
        linarith
      · have h1' : phiM (fQ L) ϱ L w u = 0 := phiM_eq_zero hϱ hw (le_of_lt hout)
        have h2' : sharpQ L u = 0 := by
          unfold sharpQ
          apply Set.indicator_of_notMem
          intro hm
          have : |u| ≤ L / 2 := abs_le.mpr ⟨hm.1, hm.2⟩
          linarith
        rw [h1', h2']
        norm_num
        exact hmaj0
  calc ∫ u, |phiM (fQ L) ϱ L w u ^ 2 - sharpQ L u|
      ≤ ∫ u, maj u := by
        apply MeasureTheory.integral_mono_of_nonneg
          (MeasureTheory.ae_of_all _ fun u => abs_nonneg _) hImaj
          (MeasureTheory.ae_of_all _ hpt)
    _ = 2 * w := by
        rw [hmaj]
        rw [MeasureTheory.integral_add
          ((MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
            (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)))
          ((MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
            (MeasureTheory.integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))),
          MeasureTheory.integral_indicator_one measurableSet_Icc,
          MeasureTheory.integral_indicator_one measurableSet_Icc,
          MeasureTheory.measureReal_def, MeasureTheory.measureReal_def,
          Real.volume_Icc, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal (by linarith)]
        ring

/-- **|g_{φ_Q}(y) − L·vConv vQuartic (y/L)| ≤ 4w for y ∈ [0, L]** (g = φ_Q² ⋆ φ_Q²). -/
theorem autocorr_phiMQsq_close (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) {y : ℝ}
    (hy0 : 0 ≤ y) (hyL : y ≤ L) :
    |Params.autocorr (fun u => phiM (fQ L) ϱ L w u ^ 2) y - L * vConv vQuartic (y / L)| ≤ 4 * w := by
  have hw0 : 0 < w := by linarith
  have hwL' : 2 * w ≤ L := by linarith
  have hL : 0 < L := by linarith
  have hf : ModFactor (fQ L) L (3/2) 12 := modFactor_fQ hL
  set h : ℝ → ℝ := fun u => phiM (fQ L) ϱ L w u ^ 2 with hhdef
  set k : ℝ → ℝ := sharpQ L with hkdef
  have hh_cont : Continuous h := ((phiM_contDiff hf hϱ hw0 hwL').pow 2).continuous
  have hh1 : ∀ u, |h u| ≤ 1 := by
    intro u
    rw [hhdef]
    simp only
    rw [abs_of_nonneg (sq_nonneg _)]
    calc phiM (fQ L) ϱ L w u ^ 2 ≤ 1 ^ 2 :=
          pow_le_pow_left₀ (phiM_nonneg hf hϱ u) (phiM_le_one hf hϱ hw0 u) 2
      _ = 1 := one_pow 2
  have hk_meas : Measurable k := by
    rw [hkdef]
    unfold sharpQ
    exact Measurable.indicator (continuous_vQuartic.comp (continuous_id.div_const L)).measurable
      measurableSet_Icc
  have hk1 : ∀ u, |k u| ≤ 1 := by
    intro u
    rw [hkdef]
    unfold sharpQ
    by_cases hm : u ∈ Set.Icc (-(L/2)) (L/2)
    · rw [Set.indicator_of_mem hm, abs_le]
      exact ⟨by linarith [(vQuartic_pos (core_mem hL (abs_le.mpr ⟨hm.1, hm.2⟩))).le], vQuartic_le_one _⟩
    · rw [Set.indicator_of_notMem hm, abs_zero]
      exact zero_le_one
  have hcs : HasCompactSupport h :=
    (phiM_hasCompactSupport (f := fQ L) hϱ (L := L) hw0).comp_left (g := fun t => t ^ 2) (by norm_num)
  have hint_h : Integrable h := hh_cont.integrable_of_hasCompactSupport hcs
  have hint_k : Integrable k := by
    rw [hkdef]
    unfold sharpQ
    exact (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr
      (((continuous_vQuartic.comp (continuous_id.div_const L)).continuousOn).integrableOn_compact
        isCompact_Icc)
  have hint_d : Integrable (fun u => h u - k u) := hint_h.sub hint_k
  have hint_hy : Integrable (fun u => h (u + y)) := hint_h.comp_add_right y
  have hint_ky : Integrable (fun u => k (u + y)) := hint_k.comp_add_right y
  have hint_dy : Integrable (fun u => h (u + y) - k (u + y)) := hint_hy.sub hint_ky
  have hmeas_hy : MeasureTheory.AEStronglyMeasurable (fun u => h (u + y)) MeasureTheory.volume :=
    hint_hy.aestronglyMeasurable
  have hint_p1 : Integrable (fun u => (h u - k u) * h (u + y)) := by
    have := hint_d.bdd_mul (c := 1) hmeas_hy (MeasureTheory.ae_of_all _ fun u => by
      rw [Real.norm_eq_abs]
      exact hh1 (u + y))
    exact this.congr (MeasureTheory.ae_of_all _ fun u => by ring)
  have hint_p2 : Integrable (fun u => k u * (h (u + y) - k (u + y))) := by
    exact hint_dy.bdd_mul (c := 1) hk_meas.aestronglyMeasurable (MeasureTheory.ae_of_all _ fun u => by
      rw [Real.norm_eq_abs]
      exact hk1 u)
  have hint_hh : Integrable (fun u => h u * h (u + y)) := by
    have := hint_h.bdd_mul (c := 1) hmeas_hy (MeasureTheory.ae_of_all _ fun u => by
      rw [Real.norm_eq_abs]
      exact hh1 (u + y))
    exact this.congr (MeasureTheory.ae_of_all _ fun u => by ring)
  have hint_kk : Integrable (fun u => k u * k (u + y)) := by
    exact hint_ky.bdd_mul (c := 1) hk_meas.aestronglyMeasurable (MeasureTheory.ae_of_all _ fun u => by
      rw [Real.norm_eq_abs]
      exact hk1 u)
  have hCk : ∫ u, k u * k (u + y) = L * vConv vQuartic (y / L) := sharpQ_autocorr_eq hL hy0 hyL
  have hdecomp : Params.autocorr h y - L * vConv vQuartic (y / L)
      = (∫ u, (h u - k u) * h (u + y)) + ∫ u, k u * (h (u + y) - k (u + y)) := by
    have e1 : Params.autocorr h y - L * vConv vQuartic (y / L)
        = ∫ u, (h u * h (u + y) - k u * k (u + y)) := by
      rw [show Params.autocorr h y = ∫ u, h u * h (u + y) from rfl, ← hCk,
        MeasureTheory.integral_sub hint_hh hint_kk]
    rw [e1, ← MeasureTheory.integral_add hint_p1 hint_p2]
    apply MeasureTheory.integral_congr_ae
    apply MeasureTheory.ae_of_all
    intro u
    ring
  have hd2w := integral_abs_phiMQsq_sub_sharp (L := L) hϱ hw0 hwL'
  have hint_dabs : Integrable (fun u => |h u - k u|) := hint_d.abs
  have hb1 : |∫ u, (h u - k u) * h (u + y)| ≤ 2 * w := by
    calc |∫ u, (h u - k u) * h (u + y)| ≤ ∫ u, |(h u - k u) * h (u + y)| :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ u, |h u - k u| := by
          apply MeasureTheory.integral_mono_of_nonneg
            (MeasureTheory.ae_of_all _ fun u => abs_nonneg _) hint_dabs
            (MeasureTheory.ae_of_all _ fun u => ?_)
          show |(h u - k u) * h (u + y)| ≤ |h u - k u|
          rw [abs_mul]
          calc |h u - k u| * |h (u + y)| ≤ |h u - k u| * 1 :=
                mul_le_mul_of_nonneg_left (hh1 (u + y)) (abs_nonneg _)
            _ = |h u - k u| := mul_one _
      _ ≤ 2 * w := hd2w
  have hb2 : |∫ u, k u * (h (u + y) - k (u + y))| ≤ 2 * w := by
    have htrans : ∫ u, |h (u + y) - k (u + y)| = ∫ u, |h u - k u| :=
      MeasureTheory.integral_add_right_eq_self (fun u => |h u - k u|) y
    calc |∫ u, k u * (h (u + y) - k (u + y))|
        ≤ ∫ u, |k u * (h (u + y) - k (u + y))| := MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ u, |h (u + y) - k (u + y)| := by
          apply MeasureTheory.integral_mono_of_nonneg
            (MeasureTheory.ae_of_all _ fun u => abs_nonneg _) (hint_dy.abs)
            (MeasureTheory.ae_of_all _ fun u => ?_)
          show |k u * (h (u + y) - k (u + y))| ≤ |h (u + y) - k (u + y)|
          rw [abs_mul]
          calc |k u| * |h (u + y) - k (u + y)| ≤ 1 * |h (u + y) - k (u + y)| :=
                mul_le_mul_of_nonneg_right (hk1 u) (abs_nonneg _)
            _ = _ := one_mul _
      _ = ∫ u, |h u - k u| := htrans
      _ ≤ 2 * w := hd2w
  calc |Params.autocorr h y - L * vConv vQuartic (y / L)|
      = |(∫ u, (h u - k u) * h (u + y)) + ∫ u, k u * (h (u + y) - k (u + y))| := by rw [hdecomp]
    _ ≤ |∫ u, (h u - k u) * h (u + y)| + |∫ u, k u * (h (u + y) - k (u + y))| := abs_add_le _ _
    _ ≤ 4 * w := by linarith

/-! ### Params-level exports -/

variable {P : Params}

theorem aV_quartic_close (hP : P.Valid) {T : ℝ} (hwL : 8 * P.w ≤ P.L T) :
    |AdmWindow.av (P.phiV vQuartic T) (P.L T) - 2777 / 3000| ≤ 2 * P.w / P.L T := by
  rw [phiV_quartic_eq]; exact aQ_close hP.taper hP.one_le_w hwL

theorem bV_quartic_close (hP : P.Valid) {T : ℝ} (hwL : 8 * P.w ≤ P.L T) :
    |AdmWindow.bv (P.phiV vQuartic T) (P.L T) - 518783 / 600000| ≤ 2 * P.w / P.L T := by
  rw [phiV_quartic_eq]; exact bQ_close hP.taper hP.one_le_w hwL

/-- b_V ≥ 1/2 (indeed ≥ 518783/600000 − 1/4) as soon as 8w ≤ L. -/
theorem bV_quartic_ge_half (hP : P.Valid) {T : ℝ} (hwL : 8 * P.w ≤ P.L T) :
    1 / 2 ≤ AdmWindow.bv (P.phiV vQuartic T) (P.L T) := by
  have h := bV_quartic_close hP hwL
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  have hq : 2 * P.w / P.L T ≤ 1 / 4 := by rw [div_le_iff₀ hL]; linarith
  linarith [(abs_le.mp h).1]

theorem gV_quartic_close_at (hP : P.Valid) {T : ℝ} (hwL : 8 * P.w ≤ P.L T) {y : ℝ}
    (hy : y ∈ Icc (0:ℝ) (P.L T)) :
    |AdmWindow.gv (P.phiV vQuartic T) y - P.L T * vConv vQuartic (y / P.L T)| ≤ 4 * P.w := by
  rw [phiV_quartic_eq]; exact autocorr_phiMQsq_close hP.taper hP.one_le_w hwL hy.1 hy.2

theorem gV_quartic_close (hP : P.Valid) :
    ∀ᶠ T in atTop, ∀ y ∈ Icc (0:ℝ) (P.L T),
      |AdmWindow.gv (P.phiV vQuartic T) y - P.L T * vConv vQuartic (y / P.L T)| ≤ 4 * P.w := by
  filter_upwards [Params.eventually_w8 hP] with T h8 y hy
  exact gV_quartic_close_at hP h8 hy

theorem gV_quartic_continuous (hP : P.Valid) {T : ℝ} (hwL : 8 * P.w ≤ P.L T) :
    Continuous (AdmWindow.gv (P.phiV vQuartic T)) :=
  (admWindow_phiV_quartic hP hwL).gv_continuous

/-- The §5 `LocalHypsCore` for the quartic data. -/
theorem localHypsCoreQ_eventually (hP : P.Valid) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      PrimeSide.LocalHypsCore (cQ P.ϱ) (P.toSetting T) (AdmWindow.localFun (P.phiV vQuartic T) (P.L T)) := by
  have hl : Tendsto l atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))
  have hL : Tendsto P.L atTop atTop := hl.const_mul_atTop hP.lam_pos
  have hX : ∀ᶠ T in atTop, 1 ≤ P.X T := by
    filter_upwards [hL.eventually_ge_atTop 0] with T h
    simpa [Params.X] using Real.one_le_exp h
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp ((hl.eventually_ge_atTop 1).and
    ((hL.eventually_ge_atTop (8 * P.w)).and hX))
  refine ⟨T₀, fun T hT => ?_⟩
  obtain ⟨h1, h8, hX1⟩ := hT₀ T hT
  exact AdmWindow.localHypsCore (P.toSetting T) (admWindow_phiV_quartic hP h8) hP.lam_pos hP.lam_le_one
    h1 hX1 (bV_quartic_ge_half hP h8)

end XiPrime
end Zeta23

end
