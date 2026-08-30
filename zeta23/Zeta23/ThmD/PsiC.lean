/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.Taper
import Zeta23.PrimeSideA.Basic

noncomputable section

open Complex MeasureTheory Real Set Filter Topology

namespace Zeta23
namespace PsiC

variable {c L w : ℝ}

/-- `ψ_c(r) := min(L, 2/|r|, c/(w r²))` (value `L` at `r = 0`), i.e. `psiA c p` with
`(p.L, p.w) = (L, w)`. -/
def psiC (c L w : ℝ) (r : ℝ) : ℝ :=
  if r = 0 then L else min L (min (2 / |r|) (c / (w * r ^ 2)))

lemma psiC_eq_psiA (c : ℝ) (p : PrimeSide.Setting) : psiC c p.L p.w = PrimeSide.psiA c p := by
  funext r; rfl

theorem psi_nonneg (hc : 4 ≤ c) (hw : 1 ≤ w) (hwL : 2 * w ≤ L) (r : ℝ) :
    0 ≤ psiC c L w r := by
  have hL : 0 ≤ L := by linarith
  have hc0 : 0 ≤ c := le_trans (by norm_num) hc
  unfold psiC
  split_ifs with hr
  · exact hL
  · exact le_min hL (le_min (by positivity) (by positivity))

theorem psi_even (r : ℝ) : psiC c L w (-r) = psiC c L w r := by
  simp [psiC]

theorem psi_le_L (_hc : 4 ≤ c) (_hw : 1 ≤ w) (_hwL : 2 * w ≤ L) (r : ℝ) :
    psiC c L w r ≤ L := by
  unfold psiC
  split_ifs with hr
  · exact le_rfl
  · exact min_le_left _ _

theorem psi_mul_abs_le (_hc : 4 ≤ c) (_hw : 1 ≤ w) (_hwL : 2 * w ≤ L) (r : ℝ) :
    psiC c L w r * |r| ≤ 2 := by
  unfold psiC
  split_ifs with hr
  · simp [hr]
  · have hra : 0 < |r| := abs_pos.mpr hr
    rw [← le_div_iff₀ hra]
    exact (min_le_right _ _).trans (min_le_left _ _)

theorem psi_mul_sq_le (hc : 4 ≤ c) (hw : 1 ≤ w) (_hwL : 2 * w ≤ L) (r : ℝ) :
    psiC c L w r * r ^ 2 ≤ c / w := by
  have hw0 : 0 < w := by linarith
  have hc0 : 0 ≤ c := le_trans (by norm_num) hc
  unfold psiC
  split_ifs with hr
  · simp [hr]; positivity
  · have hr2 : 0 < r ^ 2 := by positivity
    rw [← le_div_iff₀ hr2, div_div, mul_comm]
    exact (min_le_right _ _).trans (min_le_right _ _)

/-! #### Measurability / integrability of ψ -/

theorem psi_abs (r : ℝ) : psiC c L w |r| = psiC c L w r := by
  unfold psiC
  simp only [abs_eq_zero, abs_abs, sq_abs]

theorem psi_measurable : Measurable (psiC c L w) := by
  have h1 : Measurable (fun r : ℝ => min L (min (2 / |r|) (c / (w * r ^ 2)))) :=
    measurable_const.min ((measurable_const.div continuous_abs.measurable).min
      (measurable_const.div (measurable_const.mul (measurable_id.pow_const 2))))
  have : psiC c L w = Set.piecewise {(0:ℝ)} (fun _ => L) (fun r => min L (min (2 / |r|) (c / (w * r ^ 2)))) := by
    funext r
    unfold psiC
    by_cases hr : r = 0
    · rw [if_pos hr, Set.piecewise_eq_of_mem _ _ _ (by simp [hr])]
    · rw [if_neg hr, Set.piecewise_eq_of_notMem _ _ _ (by simp [hr])]
  rw [this]
  exact Measurable.piecewise (measurableSet_singleton 0) measurable_const h1

/-- For r > 0: ψ(r) ≤ (c_ϱ/w) · r^{−2} (rpow form). -/
theorem psi_le_rpow_neg_two (hc : 4 ≤ c) (hw : 1 ≤ w) (hwL : 2 * w ≤ L) {r : ℝ}
    (hr : 0 < r) : psiC c L w r ≤ c / w * r ^ (-2:ℝ) := by
  have h := psi_mul_sq_le hc hw hwL r
  rw [Real.rpow_neg hr.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast,
    ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  exact h

/-- The integrable majorant of ψ: L on [−1,1] and (c_ϱ/w)|r|⁻² outside. -/
noncomputable def psiMaj (c L w : ℝ) (r : ℝ) : ℝ :=
  (Icc (-1:ℝ) 1).indicator (fun _ => L) r
    + c / w * ((Ioi (1:ℝ)).indicator (fun x => x ^ (-2:ℝ)) r
      + (Ioi (1:ℝ)).indicator (fun x => x ^ (-2:ℝ)) (-r))

theorem psiMaj_integrable : Integrable (psiMaj c L w) := by
  have h1 : Integrable ((Icc (-1:ℝ) 1).indicator (fun _ => L)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))
  have h2 : Integrable ((Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ))) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).integrable_indicator measurableSet_Ioi
  have h3 : Integrable (fun r => (Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) (-r)) :=
    h2.comp_neg
  exact h1.add ((h2.add h3).const_mul _)

theorem psi_le_psiMaj (hc : 4 ≤ c) (hw : 1 ≤ w) (hwL : 2 * w ≤ L) (r : ℝ) :
    psiC c L w r ≤ psiMaj c L w r := by
  have hw0 : 0 < w := by linarith
  have hc0 : 0 ≤ c := le_trans (by norm_num) hc
  have hind : ∀ s : ℝ, 0 ≤ (Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) s := fun s =>
    Set.indicator_nonneg (fun x hx => Real.rpow_nonneg (le_trans zero_le_one (le_of_lt hx)) _) _
  unfold psiMaj
  by_cases h : r ∈ Icc (-1:ℝ) 1
  · rw [Set.indicator_of_mem h]
    have := psi_le_L hc hw hwL r
    nlinarith [hind r, hind (-r), div_nonneg hc0 hw0.le]
  · rw [Set.indicator_of_notMem h, zero_add]
    rw [mem_Icc, not_and_or, not_le, not_le] at h
    rcases h with h | h
    · -- r < -1
      have hr : 0 < -r := by linarith
      rw [Set.indicator_of_notMem (show r ∉ Ioi (1:ℝ) by simp; linarith),
        Set.indicator_of_mem (show -r ∈ Ioi (1:ℝ) by simp; linarith), zero_add]
      have := psi_le_rpow_neg_two hc hw hwL hr
      rw [← psi_abs, abs_of_neg (by linarith)]
      exact this
    · -- 1 < r
      have hr : 0 < r := by linarith
      rw [Set.indicator_of_mem (show r ∈ Ioi (1:ℝ) from h),
        Set.indicator_of_notMem (show -r ∉ Ioi (1:ℝ) by simp; linarith), add_zero]
      exact psi_le_rpow_neg_two hc hw hwL hr

/-! ### [eq:psiints].  We record upper bounds — every downstream citation of [eq:psiints] in §5 is
"≪ log L" or "≤ 8L".  (Paper: "a direct computation (split at |r| = 2/L and |r| = c_ϱ/2w; note
c_ϱ L/4w ≥ 1 by [eq:wrange]) gives Ψ₀ = 4 + 2 log(c_ϱ L/4w), ∫ψ²|r| = 8 + 8 log(c_ϱ L/4w),
∫ψ² ≤ 8L".) -/

/-- Constants for [eq:psiints]: A := 2/L ≤ B := c_ϱ/(2w) ("note c_ϱ L/4w ≥ 1 by
[eq:wrange]"), B/A = c_ϱ L/(4w). -/
theorem psiints_consts (hc : 4 ≤ c) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    0 < 2 / L ∧ 0 < c / (2 * w) ∧ 2 / L ≤ c / (2 * w) ∧
    (c / (2 * w)) / (2 / L) = c * L / (4 * w) := by
  have hc := hc
  have hL : 0 < L := by linarith
  have hw0 : 0 < w := by linarith
  refine ⟨by positivity, by positivity, ?_, ?_⟩
  · rw [div_le_div_iff₀ hL (by positivity)]; nlinarith
  · field_simp; ring

/-- On (0, ∞), ψ is dominated by the three-piece majorant L·1_{(0,A]} + (2/r)·1_{(A,B]} +
(c_ϱ/w) r⁻²·1_{(B,∞)} (in fact with equality; ≤ is all we use). -/
theorem indicator_psi_le (hc : 4 ≤ c) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) (r : ℝ) :
    (Ioi (0:ℝ)).indicator (psiC c L w) r
      ≤ (Ioc 0 (2 / L)).indicator (fun _ => L) r
        + (Ioc (2 / L) (c / (2 * w))).indicator (fun x => 2 * x⁻¹) r
        + (Ioi (c / (2 * w))).indicator (fun x => c / w * x ^ (-2:ℝ)) r := by
  obtain ⟨hA, hB, hAB, -⟩ := psiints_consts hc hw hwL
  have hwL' : 2 * w ≤ L := by linarith
  by_cases hr : r ∈ Ioi (0:ℝ)
  · have hr0 : 0 < r := hr
    rw [indicator_of_mem hr]
    by_cases h1 : r ≤ 2 / L
    · rw [indicator_of_mem (show r ∈ Ioc 0 (2 / L) from ⟨hr0, h1⟩),
        indicator_of_notMem (show r ∉ Ioc (2 / L) (c / (2 * w)) from
          fun h => not_lt.mpr h1 h.1),
        indicator_of_notMem (show r ∉ Ioi (c / (2 * w)) from
          fun h => not_lt.mpr (h1.trans hAB) h), add_zero, add_zero]
      exact psi_le_L hc hw hwL' r
    · rw [not_le] at h1
      by_cases h2 : r ≤ c / (2 * w)
      · rw [indicator_of_notMem (show r ∉ Ioc 0 (2 / L) from fun h => not_le.mpr h1 h.2),
          indicator_of_mem (show r ∈ Ioc (2 / L) (c / (2 * w)) from ⟨h1, h2⟩),
          indicator_of_notMem (show r ∉ Ioi (c / (2 * w)) from fun h => not_lt.mpr h2 h),
          zero_add, add_zero]
        have := psi_mul_abs_le hc hw hwL' r
        rw [abs_of_pos hr0] at this
        rw [← div_eq_mul_inv, le_div_iff₀ hr0]
        exact this
      · rw [not_le] at h2
        rw [indicator_of_notMem (show r ∉ Ioc 0 (2 / L) from fun h => not_le.mpr h1 h.2),
          indicator_of_notMem (show r ∉ Ioc (2 / L) (c / (2 * w)) from
            fun h => not_le.mpr h2 h.2),
          indicator_of_mem (show r ∈ Ioi (c / (2 * w)) from h2), zero_add, zero_add]
        exact psi_le_rpow_neg_two hc hw hwL' hr0
  · rw [indicator_of_notMem hr]
    have hr0 : r ≤ 0 := not_lt.mp hr
    rw [indicator_of_notMem (show r ∉ Ioc 0 (2 / L) from fun h => hr h.1),
      indicator_of_notMem (show r ∉ Ioc (2 / L) (c / (2 * w)) from
        fun h => hr (lt_trans hA h.1)),
      indicator_of_notMem (show r ∉ Ioi (c / (2 * w)) from fun h => hr (lt_trans hB h)),
      add_zero, add_zero]

/-- [eq:psiints]: Ψ₀ := ∫₀^∞ ψ(r) dr ≤ 4 + 2 log(c_ϱ L/(4w)) (paper: "="). -/
theorem integral_psi_Ioi_le (hc : 4 ≤ c) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    ∫ r in Ioi 0, psiC c L w r ≤ 4 + 2 * Real.log (c * L / (4 * w)) := by
  obtain ⟨hA, hB, hAB, hBA⟩ := psiints_consts hc hw hwL
  have hwL' : 2 * w ≤ L := by linarith
  have hL : 0 < L := by linarith
  have hw0 : 0 < w := by linarith
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) (hc)
  set A := 2 / L with hAdef
  set B := c / (2 * w) with hBdef
  -- integrability of the three pieces
  have i1 : IntegrableOn (fun _ : ℝ => L) (Ioc 0 A) := integrableOn_const (by simp)
  have i2 : IntegrableOn (fun x : ℝ => 2 * x⁻¹) (Ioc A B) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
    exact continuousOn_const.mul
      ((continuousOn_inv₀).mono fun x hx => ne_of_gt (lt_of_lt_of_le hA hx.1))
  have i3 : IntegrableOn (fun x : ℝ => c / w * x ^ (-2:ℝ)) (Ioi B) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hB).const_mul _
  have I1 := i1.integrable_indicator measurableSet_Ioc
  have I2 := i2.integrable_indicator measurableSet_Ioc
  have I3 := i3.integrable_indicator measurableSet_Ioi
  -- the three integrals
  have e1 : ∫ r, (Ioc 0 A).indicator (fun _ => L) r = 2 := by
    rw [integral_indicator measurableSet_Ioc, setIntegral_const, measureReal_def,
      Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith), smul_eq_mul, sub_zero, hAdef]
    field_simp
  have e2 : ∫ r, (Ioc A B).indicator (fun x => 2 * x⁻¹) r = 2 * Real.log (B / A) := by
    rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hAB,
      intervalIntegral.integral_const_mul, integral_inv]
    exact fun h => by
      have := (Set.mem_uIcc.mp h); rcases this with h | h <;> linarith [h.1, h.2]
  have e3 : ∫ r, (Ioi B).indicator (fun x => c / w * x ^ (-2:ℝ)) r = 2 := by
    rw [integral_indicator measurableSet_Ioi, integral_const_mul,
      integral_Ioi_rpow_of_lt (by norm_num) hB]
    norm_num
    rw [Real.rpow_neg_one, hBdef]
    field_simp
  have I12 : Integrable (fun r => (Ioc 0 A).indicator (fun _ => L) r
      + (Ioc A B).indicator (fun x => 2 * x⁻¹) r) := I1.add I2
  calc ∫ r in Ioi 0, psiC c L w r
      = ∫ r, (Ioi (0:ℝ)).indicator (psiC c L w) r := (integral_indicator measurableSet_Ioi).symm
    _ ≤ ∫ r, ((Ioc 0 A).indicator (fun _ => L) r
          + (Ioc A B).indicator (fun x => 2 * x⁻¹) r
          + (Ioi B).indicator (fun x => c / w * x ^ (-2:ℝ)) r) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun r => ?_) ((I1.add I2).add I3)
          (Eventually.of_forall fun r => indicator_psi_le hc hw hwL r)
        exact Set.indicator_nonneg (fun x _ => psi_nonneg hc hw hwL' x) _
    _ = (∫ r, ((Ioc 0 A).indicator (fun _ => L) r + (Ioc A B).indicator (fun x => 2 * x⁻¹) r))
          + ∫ r, (Ioi B).indicator (fun x => c / w * x ^ (-2:ℝ)) r := integral_add I12 I3
    _ = ((∫ r, (Ioc 0 A).indicator (fun _ => L) r) + ∫ r, (Ioc A B).indicator (fun x => 2 * x⁻¹) r)
          + ∫ r, (Ioi B).indicator (fun x => c / w * x ^ (-2:ℝ)) r := by
        rw [integral_add I1 I2]
    _ = 2 + 2 * Real.log (B / A) + 2 := by rw [e1, e2, e3]
    _ = 4 + 2 * Real.log (c * L / (4 * w)) := by rw [hBA]; ring

/-- [eq:psiints]: ∫_ℝ ψ(r)²|r| dr ≤ 8 + 8 log(c_ϱ L/(4w)) (paper: "="): split (0,2/L],
(2/L, c/2w], (c/2w, ∞): ∫₀^∞ ψ² r ≤ L²(2/L)²/2 + 4 log(cL/4w) + (c/w)²/(2(c/2w)²) = 2 + 4 log + 2. -/
theorem integral_psi_sq_mul_abs_le (hc : 4 ≤ c) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    ∫ r, psiC c L w r ^ 2 * |r| ≤ 8 + 8 * Real.log (c * L / (4 * w)) := by
  obtain ⟨hA, hB, hAB, hBA⟩ := psiints_consts hc hw hwL
  have hwL' : 2 * w ≤ L := by linarith
  have hL : 0 < L := by linarith
  have hw0 : 0 < w := by linarith
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num) (hc)
  set A := 2 / L with hAdef
  set B := c / (2 * w) with hBdef
  have hred : ∫ r, psiC c L w r ^ 2 * |r| = 2 * ∫ r in Ioi 0, psiC c L w r ^ 2 * r := by
    have h := integral_comp_abs (f := fun x => psiC c L w x ^ 2 * x)
    simp only [psi_abs] at h
    exact h
  rw [hred]
  -- majorant pieces
  have i1 : IntegrableOn (fun x : ℝ => L ^ 2 * x) (Ioc 0 A) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
    exact (continuousOn_const.mul continuousOn_id)
  have i2 : IntegrableOn (fun x : ℝ => 4 * x⁻¹) (Ioc A B) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
    exact continuousOn_const.mul
      ((continuousOn_inv₀).mono fun x hx => ne_of_gt (lt_of_lt_of_le hA hx.1))
  have i3 : IntegrableOn (fun x : ℝ => (c / w) ^ 2 * x ^ (-3:ℝ)) (Ioi B) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hB).const_mul _
  have I1 := i1.integrable_indicator measurableSet_Ioc
  have I2 := i2.integrable_indicator measurableSet_Ioc
  have I3 := i3.integrable_indicator measurableSet_Ioi
  have I12 : Integrable (fun r => (Ioc 0 A).indicator (fun x : ℝ => L ^ 2 * x) r
      + (Ioc A B).indicator (fun x : ℝ => 4 * x⁻¹) r) := I1.add I2
  have I123 : Integrable (fun r => (Ioc 0 A).indicator (fun x : ℝ => L ^ 2 * x) r
      + (Ioc A B).indicator (fun x : ℝ => 4 * x⁻¹) r
      + (Ioi B).indicator (fun x : ℝ => (c / w) ^ 2 * x ^ (-3:ℝ)) r) := I12.add I3
  have hpt : ∀ r, (Ioi (0:ℝ)).indicator (fun x => psiC c L w x ^ 2 * x) r
      ≤ (Ioc 0 A).indicator (fun x : ℝ => L ^ 2 * x) r
        + (Ioc A B).indicator (fun x : ℝ => 4 * x⁻¹) r
        + (Ioi B).indicator (fun x : ℝ => (c / w) ^ 2 * x ^ (-3:ℝ)) r := by
    intro r
    have h0 := psi_nonneg hc hw hwL' r
    by_cases hr : 0 < r
    · rw [indicator_of_mem (show r ∈ Ioi (0:ℝ) from hr)]
      by_cases h1 : r ≤ A
      · rw [indicator_of_mem (show r ∈ Ioc 0 A from ⟨hr, h1⟩),
          indicator_of_notMem (show r ∉ Ioc A B from fun h => not_lt.mpr h1 h.1),
          indicator_of_notMem (show r ∉ Ioi B from fun h => not_lt.mpr (h1.trans hAB) h),
          add_zero, add_zero]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 (psi_le_L hc hw hwL' r) 2) hr.le
      · have h1' : A < r := not_le.mp h1
        by_cases h2 : r ≤ B
        · rw [indicator_of_notMem (show r ∉ Ioc 0 A from fun h => h1 h.2),
            indicator_of_mem (show r ∈ Ioc A B from ⟨h1', h2⟩),
            indicator_of_notMem (show r ∉ Ioi B from fun h => not_lt.mpr h2 h), zero_add, add_zero]
          have h := psi_mul_abs_le hc hw hwL' r
          rw [abs_of_pos hr] at h
          -- ψ² r = (ψ r)·ψ ≤ 2 ψ ≤ 2 · (2/r)
          have h3 : psiC c L w r ≤ 2 * r⁻¹ := by
            rw [← div_eq_mul_inv, le_div_iff₀ hr]; exact h
          calc psiC c L w r ^ 2 * r = (psiC c L w r * r) * psiC c L w r := by ring
            _ ≤ 2 * (2 * r⁻¹) := mul_le_mul h h3 h0 (by norm_num)
            _ = 4 * r⁻¹ := by ring
        · have h2' : B < r := not_le.mp h2
          rw [indicator_of_notMem (show r ∉ Ioc 0 A from fun h => h1 h.2),
            indicator_of_notMem (show r ∉ Ioc A B from fun h => h2 h.2),
            indicator_of_mem (show r ∈ Ioi B from h2'), zero_add, zero_add]
          have h := psi_le_rpow_neg_two hc hw hwL' hr
          have hcw : 0 ≤ c / w * r ^ (-2:ℝ) := by positivity
          calc psiC c L w r ^ 2 * r ≤ (c / w * r ^ (-2:ℝ)) ^ 2 * r := by
                exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h 2) hr.le
            _ = (c / w) ^ 2 * r ^ (-3:ℝ) := by
                have hr' : r ≠ 0 := hr.ne'
                rw [mul_pow, ← Real.rpow_natCast (r ^ (-2:ℝ)) 2, ← Real.rpow_mul hr.le]
                norm_num
                field_simp
    · rw [indicator_of_notMem (show r ∉ Ioi (0:ℝ) from hr),
        indicator_of_notMem (show r ∉ Ioc 0 A from fun h => hr h.1),
        indicator_of_notMem (show r ∉ Ioc A B from fun h => hr (lt_trans hA h.1)),
        indicator_of_notMem (show r ∉ Ioi B from fun h => hr (lt_trans hB h)), add_zero, add_zero]
  -- the three integrals
  have e1 : ∫ r, (Ioc 0 A).indicator (fun x : ℝ => L ^ 2 * x) r = 2 := by
    rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hA.le,
      intervalIntegral.integral_const_mul, integral_id, hAdef]
    field_simp
    ring
  have e2 : ∫ r, (Ioc A B).indicator (fun x : ℝ => 4 * x⁻¹) r = 4 * Real.log (B / A) := by
    rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hAB,
      intervalIntegral.integral_const_mul, integral_inv]
    exact fun h => by
      have := (Set.mem_uIcc.mp h); rcases this with h | h <;> linarith [h.1, h.2]
  have e3 : ∫ r, (Ioi B).indicator (fun x : ℝ => (c / w) ^ 2 * x ^ (-3:ℝ)) r = 2 := by
    rw [integral_indicator measurableSet_Ioi, integral_const_mul,
      integral_Ioi_rpow_of_lt (by norm_num) hB]
    norm_num
    rw [hBdef]
    field_simp
  calc 2 * ∫ r in Ioi 0, psiC c L w r ^ 2 * r
      = 2 * ∫ r, (Ioi (0:ℝ)).indicator (fun x => psiC c L w x ^ 2 * x) r := by
        rw [integral_indicator measurableSet_Ioi]
    _ ≤ 2 * ∫ r, ((Ioc 0 A).indicator (fun x : ℝ => L ^ 2 * x) r
          + (Ioc A B).indicator (fun x : ℝ => 4 * x⁻¹) r
          + (Ioi B).indicator (fun x : ℝ => (c / w) ^ 2 * x ^ (-3:ℝ)) r) :=
        mul_le_mul_of_nonneg_left (integral_mono_of_nonneg (Eventually.of_forall fun r =>
            Set.indicator_nonneg (fun x hx => mul_nonneg (sq_nonneg _) (le_of_lt hx)) _) I123
          (Eventually.of_forall hpt)) (by norm_num)
    _ = 2 * (2 + 4 * Real.log (B / A) + 2) := by rw [integral_add I12 I3, integral_add I1 I2, e1, e2, e3]
    _ = 8 + 8 * Real.log (c * L / (4 * w)) := by rw [hBA]; ring

/-- [eq:psiints]: "∫_ℝ ψ² ≤ 8L". Uses only ψ ≤ min(L, 2/|r|):
∫ = 2∫₀^∞ ≤ 2(∫₀^{2/L} L² + ∫_{2/L}^∞ 4r⁻²) = 2(2L+2L). -/
theorem integral_psi_sq_le (hc : 4 ≤ c) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    ∫ r, psiC c L w r ^ 2 ≤ 8 * L := by
  obtain ⟨hA, -, -, -⟩ := psiints_consts hc hw hwL
  have hwL' : 2 * w ≤ L := by linarith
  have hL : 0 < L := by linarith
  set A := 2 / L with hAdef
  have hred : ∫ r, psiC c L w r ^ 2 = 2 * ∫ r in Ioi 0, psiC c L w r ^ 2 := by
    have h := integral_comp_abs (f := fun x => psiC c L w x ^ 2)
    simp only [psi_abs] at h
    exact h
  rw [hred]
  have i1 : IntegrableOn (fun _ : ℝ => L ^ 2) (Ioc 0 A) := integrableOn_const (by simp)
  have i2 : IntegrableOn (fun x : ℝ => 4 * x ^ (-2:ℝ)) (Ioi A) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hA).const_mul _
  have I1 := i1.integrable_indicator measurableSet_Ioc
  have I2 := i2.integrable_indicator measurableSet_Ioi
  have I12 : Integrable (fun r => (Ioc 0 A).indicator (fun _ : ℝ => L ^ 2) r
      + (Ioi A).indicator (fun x : ℝ => 4 * x ^ (-2:ℝ)) r) := I1.add I2
  have hpt : ∀ r, (Ioi (0:ℝ)).indicator (fun x => psiC c L w x ^ 2) r
      ≤ (Ioc 0 A).indicator (fun _ : ℝ => L ^ 2) r + (Ioi A).indicator (fun x : ℝ => 4 * x ^ (-2:ℝ)) r := by
    intro r
    have h0 := psi_nonneg hc hw hwL' r
    by_cases hr : 0 < r
    · rw [indicator_of_mem (show r ∈ Ioi (0:ℝ) from hr)]
      by_cases h1 : r ≤ A
      · rw [indicator_of_mem (show r ∈ Ioc 0 A from ⟨hr, h1⟩),
          indicator_of_notMem (show r ∉ Ioi A from fun h => not_lt.mpr h1 h), add_zero]
        exact pow_le_pow_left₀ h0 (psi_le_L hc hw hwL' r) 2
      · have h1' : A < r := not_le.mp h1
        rw [indicator_of_notMem (show r ∉ Ioc 0 A from fun h => h1 h.2),
          indicator_of_mem (show r ∈ Ioi A from h1'), zero_add]
        have h := psi_mul_abs_le hc hw hwL' r
        rw [abs_of_pos hr] at h
        have h2 : psiC c L w r ≤ 2 * r⁻¹ := by
          rw [← div_eq_mul_inv, le_div_iff₀ hr]; exact h
        calc psiC c L w r ^ 2 ≤ (2 * r⁻¹) ^ 2 := pow_le_pow_left₀ h0 h2 2
          _ = 4 * r ^ (-2:ℝ) := by
              rw [Real.rpow_neg hr.le, Real.rpow_two]; ring
    · rw [indicator_of_notMem (show r ∉ Ioi (0:ℝ) from hr),
        indicator_of_notMem (show r ∉ Ioc 0 A from fun h => hr h.1),
        indicator_of_notMem (show r ∉ Ioi A from fun h => hr (lt_trans hA h)), add_zero]
  have e1 : ∫ r, (Ioc 0 A).indicator (fun _ : ℝ => L ^ 2) r = 2 * L := by
    rw [integral_indicator measurableSet_Ioc, setIntegral_const, measureReal_def, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul, sub_zero, hAdef]
    field_simp
  have e2 : ∫ r, (Ioi A).indicator (fun x : ℝ => 4 * x ^ (-2:ℝ)) r = 2 * L := by
    rw [integral_indicator measurableSet_Ioi, integral_const_mul,
      integral_Ioi_rpow_of_lt (by norm_num) hA]
    norm_num
    rw [Real.rpow_neg_one, hAdef]
    field_simp
    ring
  calc 2 * ∫ r in Ioi 0, psiC c L w r ^ 2
      = 2 * ∫ r, (Ioi (0:ℝ)).indicator (fun x => psiC c L w x ^ 2) r := by
        rw [integral_indicator measurableSet_Ioi]
    _ ≤ 2 * ∫ r, ((Ioc 0 A).indicator (fun _ : ℝ => L ^ 2) r
          + (Ioi A).indicator (fun x : ℝ => 4 * x ^ (-2:ℝ)) r) :=
        mul_le_mul_of_nonneg_left (integral_mono_of_nonneg
          (Eventually.of_forall fun r => Set.indicator_nonneg (fun x _ => sq_nonneg _) _) I12
          (Eventually.of_forall hpt)) (by norm_num)
    _ = 2 * (2 * L + 2 * L) := by rw [integral_add I1 I2, e1, e2]
    _ = 8 * L := by ring

theorem psi_integrable (hc : 4 ≤ c) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    Integrable (psiC c L w) := by
  have hwL' : 2 * w ≤ L := by linarith
  refine (psiMaj_integrable (c := c) (L := L) (w := w)).mono'
    psi_measurable.aestronglyMeasurable (Eventually.of_forall fun r => ?_)
  rw [Real.norm_of_nonneg (psi_nonneg hc hw hwL' r)]
  exact psi_le_psiMaj hc hw hwL' r

theorem psi_sq_integrable (hc : 4 ≤ c) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    Integrable (fun r => psiC c L w r ^ 2) := by
  have hwL' : 2 * w ≤ L := by linarith
  refine ((psi_integrable hc hw hwL).const_mul L).mono'
    (psi_measurable.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun r => ?_)
  have h0 := psi_nonneg hc hw hwL' r
  have h1 := psi_le_L hc hw hwL' r
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  nlinarith

theorem psi_sq_mul_abs_integrable (hc : 4 ≤ c) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    Integrable (fun r => psiC c L w r ^ 2 * |r|) := by
  have hwL' : 2 * w ≤ L := by linarith
  refine ((psi_integrable hc hw hwL).const_mul 2).mono'
    ((psi_measurable.pow_const 2).mul continuous_abs.measurable).aestronglyMeasurable
    (Eventually.of_forall fun r => ?_)
  have h0 := psi_nonneg hc hw hwL' r
  have h1 := psi_mul_abs_le hc hw hwL' r
  rw [Real.norm_of_nonneg (by positivity)]
  nlinarith

/-! #### Generic moment bounds from |F| ≤ ψ-type information -/

/-- If |F| ≤ ψ pointwise then ∫ F²|r| ≤ ∫ ψ²|r| ≤ 8 + 8 log(c_ϱ L/4w). -/
theorem integral_sq_mul_abs_le_of_le_psi (hc : 4 ≤ c) (hw : 1 ≤ w)
    (hwL : 8 * w ≤ L) {F : ℝ → ℝ} (hF : ∀ r, |F r| ≤ psiC c L w r) :
    ∫ r, F r ^ 2 * |r| ≤ 8 + 8 * Real.log (c * L / (4 * w)) := by
  refine le_trans (integral_mono_of_nonneg (Eventually.of_forall fun r => by positivity)
    (psi_sq_mul_abs_integrable hc hw hwL) (Eventually.of_forall fun r => ?_))
    (integral_psi_sq_mul_abs_le hc hw hwL)
  have h : F r ^ 2 ≤ psiC c L w r ^ 2 := by
    rw [← sq_abs (F r)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hF r) 2
  exact mul_le_mul_of_nonneg_right h (abs_nonneg r)

/-- The integrable majorant for the r²-moments: 4 on [−1,1] and C²|r|⁻² outside. -/
noncomputable def momMaj (C : ℝ) (r : ℝ) : ℝ :=
  (Icc (-1:ℝ) 1).indicator (fun _ => (4:ℝ)) r
    + C ^ 2 * ((Ioi (1:ℝ)).indicator (fun x => x ^ (-2:ℝ)) r
      + (Ioi (1:ℝ)).indicator (fun x => x ^ (-2:ℝ)) (-r))

theorem momMaj_integrable (C : ℝ) : Integrable (momMaj C) := by
  have h1 : Integrable ((Icc (-1:ℝ) 1).indicator (fun _ => (4:ℝ))) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))
  have h2 : Integrable ((Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ))) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).integrable_indicator measurableSet_Ioi
  have h3 : Integrable (fun r => (Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) (-r)) :=
    h2.comp_neg
  exact h1.add ((h2.add h3).const_mul _)

theorem integral_momMaj (C : ℝ) : ∫ r, momMaj C r = 8 + 2 * C ^ 2 := by
  have h1 : Integrable ((Icc (-1:ℝ) 1).indicator (fun _ => (4:ℝ))) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))
  have h2 : Integrable ((Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ))) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).integrable_indicator measurableSet_Ioi
  have h3 : Integrable (fun r => (Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) (-r)) :=
    h2.comp_neg
  have e1 : ∫ r, (Icc (-1:ℝ) 1).indicator (fun _ => (4:ℝ)) r = 8 := by
    rw [integral_indicator measurableSet_Icc, setIntegral_const, measureReal_def,
      Real.volume_Icc, ENNReal.toReal_ofReal (by norm_num), smul_eq_mul]
    norm_num
  have e2 : ∫ r, (Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) r = 1 := by
    rw [integral_indicator measurableSet_Ioi, integral_Ioi_rpow_of_lt (by norm_num) one_pos]
    norm_num
  have e3 : ∫ r, (Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) (-r) = 1 := by
    have hneg := MeasureTheory.integral_neg_eq_self
      ((Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ))) volume
    rw [hneg]
    exact e2
  have h23 : Integrable (fun r => (Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) r
      + (Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) (-r)) := h2.add h3
  unfold momMaj
  calc ∫ r, ((Icc (-1:ℝ) 1).indicator (fun _ => (4:ℝ)) r
        + C ^ 2 * ((Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) r
          + (Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) (-r)))
      = (∫ r, (Icc (-1:ℝ) 1).indicator (fun _ => (4:ℝ)) r)
        + ∫ r, C ^ 2 * ((Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) r
          + (Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) (-r)) :=
        integral_add h1 (h23.const_mul _)
    _ = 8 + C ^ 2 * ((∫ r, (Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) r)
          + ∫ r, (Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) (-r)) := by
        rw [e1, integral_const_mul]
        congr 2
        exact integral_add h2 h3
    _ = 8 + 2 * C ^ 2 := by rw [e2, e3]; ring

/-- Pointwise: |F(r)|·|r| ≤ 2 and |F(r)|·r² ≤ C give F(r)² r² ≤ momMaj C r. -/
theorem sq_mul_sq_le_momMaj {F : ℝ → ℝ} {C : ℝ} (_hC : 0 ≤ C)
    (h1 : ∀ r, |F r| * |r| ≤ 2) (h2 : ∀ r, |F r| * r ^ 2 ≤ C) (r : ℝ) :
    F r ^ 2 * r ^ 2 ≤ momMaj C r := by
  have hind : ∀ s : ℝ, 0 ≤ (Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) s := fun s =>
    Set.indicator_nonneg (fun x hx => Real.rpow_nonneg (le_trans zero_le_one (le_of_lt hx)) _) _
  have hsq : ∀ s : ℝ, 1 < s → F r ^ 2 * s ^ 2 * s ^ 2 ≤ C ^ 2 → F r ^ 2 * s ^ 2 ≤ C ^ 2 * s ^ (-2:ℝ) := by
    intro s hs h
    have hs0 : 0 < s := by linarith
    rw [Real.rpow_neg hs0.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast,
      ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    exact h
  unfold momMaj
  by_cases h : r ∈ Icc (-1:ℝ) 1
  · rw [Set.indicator_of_mem h]
    have hb : F r ^ 2 * r ^ 2 ≤ 4 := by
      have := h1 r
      have h0 : 0 ≤ |F r| * |r| := by positivity
      calc F r ^ 2 * r ^ 2 = (|F r| * |r|) ^ 2 := by rw [mul_pow, sq_abs, sq_abs]
        _ ≤ 2 ^ 2 := pow_le_pow_left₀ h0 this 2
        _ = 4 := by norm_num
    nlinarith [hind r, hind (-r), sq_nonneg C]
  · rw [Set.indicator_of_notMem h, zero_add]
    rw [mem_Icc, not_and_or, not_le, not_le] at h
    have hFsq : F r ^ 2 * r ^ 2 * r ^ 2 ≤ C ^ 2 := by
      have := h2 r
      have h0 : 0 ≤ |F r| * r ^ 2 := by positivity
      calc F r ^ 2 * r ^ 2 * r ^ 2 = (|F r| * r ^ 2) ^ 2 := by rw [mul_pow, sq_abs]; ring
        _ ≤ C ^ 2 := pow_le_pow_left₀ h0 this 2
    rcases h with h | h
    · -- r < -1
      rw [Set.indicator_of_notMem (show r ∉ Ioi (1:ℝ) by simp; linarith),
        Set.indicator_of_mem (show -r ∈ Ioi (1:ℝ) by simp; linarith), zero_add]
      have := hsq (-r) (by linarith) (by simpa using hFsq)
      simpa using this
    · -- 1 < r
      rw [Set.indicator_of_mem (show r ∈ Ioi (1:ℝ) from h),
        Set.indicator_of_notMem (show -r ∉ Ioi (1:ℝ) by simp; linarith), add_zero]
      exact hsq r h hFsq

theorem integrable_sq_mul_sq_of_bounds {F : ℝ → ℝ} {C : ℝ} (hFc : Continuous F)
    (hC : 0 ≤ C) (h1 : ∀ r, |F r| * |r| ≤ 2) (h2 : ∀ r, |F r| * r ^ 2 ≤ C) :
    Integrable (fun r => F r ^ 2 * r ^ 2) := by
  refine (momMaj_integrable C).mono' (by fun_prop) (Eventually.of_forall fun r => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact sq_mul_sq_le_momMaj hC h1 h2 r

theorem integral_sq_mul_sq_le_of_bounds {F : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (h1 : ∀ r, |F r| * |r| ≤ 2) (h2 : ∀ r, |F r| * r ^ 2 ≤ C) :
    ∫ r, F r ^ 2 * r ^ 2 ≤ 8 + 2 * C ^ 2 := by
  rw [← integral_momMaj C]
  exact integral_mono_of_nonneg (Eventually.of_forall fun r => by positivity)
    (momMaj_integrable C) (Eventually.of_forall fun r => sq_mul_sq_le_momMaj hC h1 h2 r)


end PsiC
end Zeta23

end
