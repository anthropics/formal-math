/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib
import Zeta23.Taper.Basic

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform

namespace Zeta23

namespace Taper

theorem taperProfile_smoothstep : TaperProfile smoothstep where
  contDiff := Real.smoothTransition.contDiff
  monotone := Real.smoothTransition.monotone
  eq_zero := fun _ hx => Real.smoothTransition.zero_of_nonpos hx
  eq_one := fun _ hx => Real.smoothTransition.one_of_one_le hx

/-! ### [eq:phinorms] -/

section Norms
variable {ϱ : ℝ → ℝ} {L w : ℝ}

/-- A monotone function has nonnegative derivative wherever it is differentiable. -/
private lemma deriv_nonneg_of_monotone {f : ℝ → ℝ} (hf : Monotone f) {y : ℝ}
    (hd : DifferentiableAt ℝ f y) : 0 ≤ deriv f y := by
  have h := hd.hasDerivAt
  rw [hasDerivAt_iff_tendsto_slope] at h
  refine ge_of_tendsto h ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  rcases lt_or_gt_of_ne (hx : x ≠ y) with hlt | hgt
  · rw [slope_def_field]
    have h := div_nonneg (show (0 : ℝ) ≤ f y - f x by linarith [hf hlt.le])
      (show (0 : ℝ) ≤ y - x by linarith)
    rwa [show (f y - f x) / (y - x) = (f x - f y) / (x - y) by
      rw [← neg_sub (f x) (f y), ← neg_sub x y, neg_div_neg_eq]] at h
  · rw [slope_def_field]
    exact div_nonneg (by linarith [hf hgt.le]) (by linarith)

private lemma rho_differentiable (hϱ : TaperProfile ϱ) : Differentiable ℝ ϱ :=
  hϱ.contDiff.differentiable (by norm_num)

/-- For u > 0, φ′(u) = −ϱ′((L/2 − u)/w)/w. -/
private lemma deriv_phi_pos (hϱ : TaperProfile ϱ) (_hw : 0 < w) {u : ℝ} (hu : 0 < u) :
    deriv (phi ϱ L w) u = -(deriv ϱ ((L / 2 - u) / w) / w) := by
  have hev : phi ϱ L w =ᶠ[nhds u] (fun v => ϱ ((L / 2 - v) / w)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
    unfold phi
    rw [abs_of_pos hv]
  rw [hev.deriv_eq]
  have hg : HasDerivAt (fun v : ℝ => (L / 2 - v) / w) (-1 / w) u := by
    have h1 : HasDerivAt (fun v : ℝ => L / 2 - v) (-1) u := (hasDerivAt_id u).const_sub (L / 2)
    exact h1.div_const w
  have hϱd : HasDerivAt ϱ (deriv ϱ ((L / 2 - u) / w)) ((L / 2 - u) / w) :=
    (rho_differentiable hϱ _).hasDerivAt
  have hcomp : HasDerivAt (fun v : ℝ => ϱ ((L / 2 - v) / w))
      (deriv ϱ ((L / 2 - u) / w) * (-1 / w)) u := hϱd.comp u hg
  rw [hcomp.deriv]
  ring

/-- ∫ℝ |F′| = 2 for an even C¹ bump: F(0) = 1, F = 0 off [−L/2, L/2], F′ ≤ 0 on (0,∞). -/
private lemma integral_abs_deriv_eq_two {F : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hF : ContDiff ℝ 1 F) (heven : ∀ u, F (-u) = F u)
    (hnonpos : ∀ u : ℝ, 0 < u → deriv F u ≤ 0)
    (hsupp : ∀ u : ℝ, L / 2 ≤ |u| → F u = 0) (hF0 : F 0 = 1) :
    ∫ u, |deriv F u| = 2 := by
  have hdcont : Continuous (deriv F) := hF.continuous_deriv le_rfl
  have hodd : ∀ u : ℝ, deriv F (-u) = -(deriv F u) := by
    intro u
    have h1 : deriv (fun x : ℝ => F (-x)) u = -deriv F (-u) := deriv_comp_neg F u
    have h2 : (fun x : ℝ => F (-x)) = F := funext heven
    rw [h2] at h1
    linarith
  have hzero_out : ∀ u : ℝ, L / 2 < |u| → deriv F u = 0 := by
    intro u hu
    have hopen : IsOpen {v : ℝ | L / 2 < |v|} := isOpen_lt continuous_const continuous_abs
    have hev : F =ᶠ[nhds u] (fun _ => (0 : ℝ)) := by
      filter_upwards [hopen.mem_nhds hu] with v hv
      exact hsupp v (le_of_lt hv)
    rw [hev.deriv_eq]
    simp
  have heqIcc : ∫ u, |deriv F u| = ∫ u in Icc (-(L / 2)) (L / 2), |deriv F u| := by
    refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => ?_).symm
    rw [mem_Icc, not_and_or, not_le, not_le] at hu
    have : L / 2 < |u| := by
      rcases hu with h | h
      · calc L / 2 < -u := by linarith
          _ ≤ |u| := neg_le_abs u
      · calc L / 2 < u := h
          _ ≤ |u| := le_abs_self u
    rw [hzero_out u this, abs_zero]
  have hIccIoc : ∫ u in Icc (-(L / 2)) (L / 2), |deriv F u|
      = ∫ u in (-(L / 2))..(L / 2), |deriv F u| := by
    rw [intervalIntegral.integral_of_le (by linarith), MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hii : ∀ a b : ℝ, IntervalIntegrable (fun u => |deriv F u|) MeasureTheory.volume a b :=
    fun a b => (hdcont.abs).intervalIntegrable a b
  have hsplit : ∫ u in (-(L / 2))..(L / 2), |deriv F u|
      = (∫ u in (-(L / 2))..(0 : ℝ), |deriv F u|) + ∫ u in (0 : ℝ)..(L / 2), |deriv F u| :=
    (intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _)).symm
  have hright : ∫ u in (0 : ℝ)..(L / 2), |deriv F u| = 1 := by
    have habs : ∫ u in (0 : ℝ)..(L / 2), |deriv F u|
        = ∫ u in (0 : ℝ)..(L / 2), -(deriv F u) := by
      rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le
        (by linarith)]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
      exact abs_of_nonpos (hnonpos u hu.1)
    rw [habs, intervalIntegral.integral_neg, intervalIntegral.integral_deriv_eq_sub
      (fun x _ => (hF.differentiable (by norm_num)).differentiableAt) (hdcont.intervalIntegrable _ _)]
    rw [hsupp (L / 2) (by rw [abs_of_pos (by linarith)]), hF0]
    ring
  have hleft : ∫ u in (-(L / 2))..(0 : ℝ), |deriv F u|
      = ∫ u in (0 : ℝ)..(L / 2), |deriv F u| := by
    have h1 := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := L / 2)
      (fun u => |deriv F u|)
    have h2 : (∫ x in (0 : ℝ)..(L / 2), |deriv F (-x)|)
        = ∫ x in (0 : ℝ)..(L / 2), |deriv F x| := by
      refine intervalIntegral.integral_congr fun x _ => ?_
      rw [hodd, abs_neg]
    rw [← h2, h1]
    norm_num
  rw [heqIcc, hIccIoc, hsplit, hleft, hright]
  ring

/-- [eq:phinorms]: "`‖φ'‖₁ = 2`". -/
theorem integral_abs_deriv_phi (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ∫ u, |deriv (phi ϱ L w) u| = 2 := by
  refine integral_abs_deriv_eq_two (by linarith) ((phi_contDiff hϱ hw hwL).of_le (by norm_num))
    phi_even (fun u hu => ?_) (fun u hu => phi_eq_zero hϱ hw hu) (phi_eq_one hϱ hw (by
      rw [abs_zero]; linarith))
  rw [deriv_phi_pos hϱ hw hu]
  have h1 : 0 ≤ deriv ϱ ((L / 2 - u) / w) :=
    deriv_nonneg_of_monotone hϱ.monotone (rho_differentiable hϱ _)
  have h2 : 0 ≤ deriv ϱ ((L / 2 - u) / w) / w := div_nonneg h1 hw.le
  linarith

/-- [eq:phinorms]: "`‖(φ²)'‖₁ = 2`". -/
theorem integral_abs_deriv_phi_sq (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ∫ u, |deriv (fun u => phi ϱ L w u ^ 2) u| = 2 := by
  have hφ1 : ContDiff ℝ 1 (phi ϱ L w) := (phi_contDiff hϱ hw hwL).of_le (by norm_num)
  have hderiv_sq : ∀ u : ℝ, deriv (fun u => phi ϱ L w u ^ 2) u
      = 2 * phi ϱ L w u * deriv (phi ϱ L w) u := by
    intro u
    have hd : HasDerivAt (phi ϱ L w) (deriv (phi ϱ L w) u) u :=
      ((hφ1.differentiable (by norm_num)) u).hasDerivAt
    have hpow : HasDerivAt (fun v => phi ϱ L w v ^ 2)
        ((2 : ℕ) * phi ϱ L w u ^ (2 - 1) * deriv (phi ϱ L w) u) u := hd.pow 2
    rw [hpow.deriv]
    norm_num
  refine integral_abs_deriv_eq_two (L := L) (by linarith) (hφ1.pow 2)
    (fun u => by rw [phi_even]) (fun u hu => ?_) (fun u hu => by
      rw [phi_eq_zero hϱ hw hu]; ring) (by
      rw [phi_eq_one hϱ hw (by rw [abs_zero]; linarith)]; ring)
  rw [hderiv_sq u]
  have h1 : 0 ≤ phi ϱ L w u := phi_nonneg hϱ u
  have h2 : deriv (phi ϱ L w) u ≤ 0 := by
    rw [deriv_phi_pos hϱ hw hu]
    have := deriv_nonneg_of_monotone hϱ.monotone
      (rho_differentiable hϱ ((L / 2 - u) / w))
    have h3 : 0 ≤ deriv ϱ ((L / 2 - u) / w) / w := div_nonneg this hw.le
    linarith
  nlinarith


/-- deriv ϱ vanishes left of 0 (ϱ is locally 0 there). -/
private lemma derivRho_zero_left (hϱ : TaperProfile ϱ) {x : ℝ} (hx : x < 0) : deriv ϱ x = 0 := by
  have hev : ϱ =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Iio.mem_nhds hx] with v hv
    exact hϱ.eq_zero v (le_of_lt hv)
  rw [hev.deriv_eq]
  simp

/-- deriv ϱ vanishes right of 1 (ϱ is locally 1 there). -/
private lemma derivRho_zero_right (hϱ : TaperProfile ϱ) {x : ℝ} (hx : 1 < x) : deriv ϱ x = 0 := by
  have hev : ϱ =ᶠ[nhds x] (fun _ => (1 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with v hv
    exact hϱ.eq_one v (le_of_lt hv)
  rw [hev.deriv_eq]
  simp

private lemma derivRho2_zero_left (hϱ : TaperProfile ϱ) {x : ℝ} (hx : x < 0) :
    deriv (deriv ϱ) x = 0 := by
  have hev : deriv ϱ =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Iio.mem_nhds hx] with v hv
    exact derivRho_zero_left hϱ hv
  rw [hev.deriv_eq]
  simp

private lemma derivRho2_zero_right (hϱ : TaperProfile ϱ) {x : ℝ} (hx : 1 < x) :
    deriv (deriv ϱ) x = 0 := by
  have hev : deriv ϱ =ᶠ[nhds x] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with v hv
    exact derivRho_zero_right hϱ hv
  rw [hev.deriv_eq]
  simp

private lemma derivRho_continuous (hϱ : TaperProfile ϱ) : Continuous (deriv ϱ) :=
  hϱ.contDiff.continuous_deriv (by norm_num)

private lemma bddAbove_abs_derivRho (hϱ : TaperProfile ϱ) :
    BddAbove (Set.range fun x => |deriv ϱ x|) := by
  have hcs : HasCompactSupport (deriv ϱ) := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (0 : ℝ)) (b := 1))
      fun x hx => ?_
    rw [Function.mem_support] at hx
    by_contra h
    rw [mem_Icc, not_and_or, not_le, not_le] at h
    rcases h with h | h
    · exact hx (derivRho_zero_left hϱ h)
    · exact hx (derivRho_zero_right hϱ h)
  exact (derivRho_continuous hϱ).abs.bddAbove_range_of_hasCompactSupport
    (hcs.comp_left (g := fun t => |t|) abs_zero)

private lemma abs_derivRho_le (hϱ : TaperProfile ϱ) (y : ℝ) : |deriv ϱ y| ≤ supDeriv ϱ :=
  le_ciSup (bddAbove_abs_derivRho hϱ) y

private lemma supDeriv_nonneg (hϱ : TaperProfile ϱ) : 0 ≤ supDeriv ϱ :=
  le_trans (abs_nonneg _) (abs_derivRho_le hϱ 0)

private lemma l1Deriv2_nonneg (ϱ : ℝ → ℝ) : 0 ≤ l1Deriv2 ϱ :=
  MeasureTheory.integral_nonneg fun _ => abs_nonneg _

private lemma deriv_phi_odd (_hϱ : TaperProfile ϱ) (v : ℝ) :
    deriv (phi ϱ L w) (-v) = -(deriv (phi ϱ L w) v) := by
  have h1 : deriv (fun x : ℝ => phi ϱ L w (-x)) v = -deriv (phi ϱ L w) (-v) :=
    deriv_comp_neg _ _
  have h2 : (fun x : ℝ => phi ϱ L w (-x)) = phi ϱ L w := funext fun x => phi_even x
  rw [h2] at h1
  linarith

/-- [eq:phinorms]: "`‖φ'‖_∞ = ‖ϱ'‖_∞ / w`" (we record `≤`, which is what is used). -/
theorem abs_deriv_phi_le (hϱ : TaperProfile ϱ) (hw : 0 < w) (_hwL : 2 * w ≤ L) (u : ℝ) :
    |deriv (phi ϱ L w) u| ≤ supDeriv ϱ / w := by
  have key : ∀ v : ℝ, 0 < v → |deriv (phi ϱ L w) v| ≤ supDeriv ϱ / w := by
    intro v hv
    rw [deriv_phi_pos hϱ hw hv, abs_neg, abs_div, abs_of_pos hw]
    gcongr
    exact abs_derivRho_le hϱ _
  rcases lt_trichotomy u 0 with hu | hu | hu
  · have heq : deriv (phi ϱ L w) u = -(deriv (phi ϱ L w) (-u)) := by
      have := deriv_phi_odd hϱ (L := L) (w := w) (-u)
      rwa [neg_neg] at this
    rw [heq, abs_neg]
    exact key (-u) (by linarith)
  · subst hu
    have h0 : deriv (phi ϱ L w) 0 = 0 := by
      have := deriv_phi_odd hϱ (L := L) (w := w) 0
      rw [neg_zero] at this
      linarith
    rw [h0, abs_zero]
    have := supDeriv_nonneg hϱ
    positivity
  · exact key u hu

/-- For u > 0, φ″(u) = ϱ″((L/2 − u)/w)/w². -/
private lemma deriv2_phi_pos (hϱ : TaperProfile ϱ) (hw : 0 < w) {u : ℝ} (hu : 0 < u) :
    deriv (deriv (phi ϱ L w)) u = deriv (deriv ϱ) ((L / 2 - u) / w) / w ^ 2 := by
  have hev : deriv (phi ϱ L w) =ᶠ[nhds u] (fun v => -(deriv ϱ ((L / 2 - v) / w) / w)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
    exact deriv_phi_pos hϱ hw hv
  rw [hev.deriv_eq]
  have hg : HasDerivAt (fun v : ℝ => (L / 2 - v) / w) (-1 / w) u := by
    have h1 : HasDerivAt (fun v : ℝ => L / 2 - v) (-1) u := (hasDerivAt_id u).const_sub (L / 2)
    exact h1.div_const w
  have hd2 : HasDerivAt (deriv ϱ) (deriv (deriv ϱ) ((L / 2 - u) / w)) ((L / 2 - u) / w) :=
    ((hϱ.contDiff.deriv' (n := 2)).differentiable (by norm_num) _).hasDerivAt
  have hcomp0 : HasDerivAt ((deriv ϱ) ∘ fun v : ℝ => (L / 2 - v) / w)
      (deriv (deriv ϱ) ((L / 2 - u) / w) * (-1 / w)) u := hd2.comp u hg
  have hcomp : HasDerivAt (fun v : ℝ => deriv ϱ ((L / 2 - v) / w))
      (deriv (deriv ϱ) ((L / 2 - u) / w) * (-1 / w)) u := hcomp0
  have hneg : HasDerivAt (fun v : ℝ => -(deriv ϱ ((L / 2 - v) / w) / w))
      (-(deriv (deriv ϱ) ((L / 2 - u) / w) * (-1 / w) / w)) u := (hcomp.div_const w).neg
  rw [hneg.deriv]
  field_simp

/-- Even-integrand reduction: ∫ℝ |G| = 2∫₀^{L/2} |G| for |G| even, G = 0 off [−L/2, L/2]. -/
private lemma integral_abs_eq_two_mul {G : ℝ → ℝ} {L : ℝ} (hL : 0 < L) (hcont : Continuous G)
    (habs_even : ∀ u, |G (-u)| = |G u|) (hzero : ∀ u : ℝ, L / 2 < |u| → G u = 0) :
    ∫ u, |G u| = 2 * ∫ u in (0 : ℝ)..(L / 2), |G u| := by
  have heqIcc : ∫ u, |G u| = ∫ u in Icc (-(L / 2)) (L / 2), |G u| := by
    refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => ?_).symm
    rw [mem_Icc, not_and_or, not_le, not_le] at hu
    have habs : L / 2 < |u| := by
      rcases hu with h | h
      · calc L / 2 < -u := by linarith
          _ ≤ |u| := neg_le_abs u
      · calc L / 2 < u := h
          _ ≤ |u| := le_abs_self u
    rw [hzero u habs, abs_zero]
  have hIccIoc : ∫ u in Icc (-(L / 2)) (L / 2), |G u|
      = ∫ u in (-(L / 2))..(L / 2), |G u| := by
    rw [intervalIntegral.integral_of_le (by linarith), MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hii : ∀ a b : ℝ, IntervalIntegrable (fun u => |G u|) MeasureTheory.volume a b :=
    fun a b => (hcont.abs).intervalIntegrable a b
  have hsplit : ∫ u in (-(L / 2))..(L / 2), |G u|
      = (∫ u in (-(L / 2))..(0 : ℝ), |G u|) + ∫ u in (0 : ℝ)..(L / 2), |G u| :=
    (intervalIntegral.integral_add_adjacent_intervals (hii _ _) (hii _ _)).symm
  have hleft : ∫ u in (-(L / 2))..(0 : ℝ), |G u| = ∫ u in (0 : ℝ)..(L / 2), |G u| := by
    have h1 := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := L / 2)
      (fun u => |G u|)
    have h2 : (∫ x in (0 : ℝ)..(L / 2), |G (-x)|) = ∫ x in (0 : ℝ)..(L / 2), |G x| :=
      intervalIntegral.integral_congr fun x _ => habs_even x
    rw [← h2, h1]
    norm_num
  rw [heqIcc, hIccIoc, hsplit, hleft]
  ring

private lemma deriv_phi_contDiff (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ContDiff ℝ 2 (deriv (phi ϱ L w)) :=
  (phi_contDiff hϱ hw hwL).deriv' (n := 2)

private lemma deriv2_phi_even (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (v : ℝ) :
    deriv (deriv (phi ϱ L w)) (-v) = deriv (deriv (phi ϱ L w)) v := by
  have h1 : deriv (fun x : ℝ => deriv (phi ϱ L w) (-x)) v
      = -deriv (deriv (phi ϱ L w)) (-v) := deriv_comp_neg _ _
  have h2 : (fun x : ℝ => deriv (phi ϱ L w) (-x)) = fun x => -(deriv (phi ϱ L w) x) :=
    funext (deriv_phi_odd hϱ)
  rw [h2] at h1
  have h3 : deriv (fun x : ℝ => -(deriv (phi ϱ L w) x)) v
      = -(deriv (deriv (phi ϱ L w)) v) :=
    ((((deriv_phi_contDiff hϱ hw hwL).differentiable (by norm_num)) v).hasDerivAt.neg).deriv
  rw [h3] at h1
  linarith

private lemma deriv2_phi_zero_out (hϱ : TaperProfile ϱ) (hw : 0 < w) {u : ℝ}
    (hu : L / 2 < |u|) : deriv (deriv (phi ϱ L w)) u = 0 := by
  have hopen : IsOpen {v : ℝ | L / 2 < |v|} := isOpen_lt continuous_const continuous_abs
  have hev : deriv (phi ϱ L w) =ᶠ[nhds u] (fun _ => (0 : ℝ)) := by
    filter_upwards [hopen.mem_nhds hu] with v hv
    have hφ0 : phi ϱ L w =ᶠ[nhds v] (fun _ => (0 : ℝ)) := by
      filter_upwards [hopen.mem_nhds hv] with x hx
      exact phi_eq_zero hϱ hw (le_of_lt hx)
    rw [hφ0.deriv_eq]
    simp
  rw [hev.deriv_eq]
  simp

/-- [eq:phinorms]: "`‖φ''‖₁ = 2‖ϱ''‖₁ / w`". -/
theorem integral_abs_deriv2_phi (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ∫ u, |deriv (deriv (phi ϱ L w)) u| = 2 * l1Deriv2 ϱ / w := by
  have hL : (0 : ℝ) < L := by linarith
  have hcont2 : Continuous (deriv (deriv (phi ϱ L w))) :=
    (deriv_phi_contDiff hϱ hw hwL).continuous_deriv (by norm_num)
  rw [integral_abs_eq_two_mul hL hcont2
    (fun u => by rw [deriv2_phi_even hϱ hw hwL]) (fun u hu => deriv2_phi_zero_out hϱ hw hu)]
  have hcongr : ∫ u in (0 : ℝ)..(L / 2), |deriv (deriv (phi ϱ L w)) u|
      = ∫ u in (0 : ℝ)..(L / 2), |deriv (deriv ϱ) ((L / 2 - u) / w)| / w ^ 2 := by
    rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le
      (by linarith)]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
    rw [deriv2_phi_pos hϱ hw hu.1, abs_div, abs_of_pos (by positivity : (0 : ℝ) < w ^ 2)]
  rw [hcongr]
  have hsub1 : ∫ u in (0 : ℝ)..(L / 2), |deriv (deriv ϱ) ((L / 2 - u) / w)| / w ^ 2
      = ∫ y in (0 : ℝ)..(L / 2), |deriv (deriv ϱ) (y / w)| / w ^ 2 := by
    have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := L / 2)
      (fun y => |deriv (deriv ϱ) (y / w)| / w ^ 2) (L / 2)
    simpa using h
  rw [hsub1]
  have hdiv : ∫ y in (0 : ℝ)..(L / 2), |deriv (deriv ϱ) (y / w)| / w ^ 2
      = (∫ y in (0 : ℝ)..(L / 2), |deriv (deriv ϱ) (y / w)|) / w ^ 2 :=
    intervalIntegral.integral_div _ _
  rw [hdiv]
  have hsub2 : ∫ y in (0 : ℝ)..(L / 2), |deriv (deriv ϱ) (y / w)|
      = w * ∫ y in (0 : ℝ)..(L / (2 * w)), |deriv (deriv ϱ) y| := by
    have h := intervalIntegral.integral_comp_div (a := (0 : ℝ)) (b := L / 2)
      (f := fun y => |deriv (deriv ϱ) y|) (ne_of_gt hw)
    rw [h, smul_eq_mul]
    norm_num [div_div]
  rw [hsub2]
  have hfull : ∫ y in (0 : ℝ)..(L / (2 * w)), |deriv (deriv ϱ) y| = l1Deriv2 ϱ := by
    have hone : (1 : ℝ) ≤ L / (2 * w) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    unfold l1Deriv2
    rw [intervalIntegral.integral_of_le (by linarith),
      ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm.symm
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with h | h
    · rw [derivRho2_zero_left hϱ h, abs_zero]
    · rw [derivRho2_zero_right hϱ (by linarith), abs_zero]
  rw [hfull]
  field_simp

/-- [eq:phinorms]: "`‖(φ²)''‖₁ ≤ c_ϱ / w`" (uses `w ≥ 1`). -/
theorem integral_abs_deriv2_phi_sq_le (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 2 * w ≤ L) :
    ∫ u, |deriv (deriv (fun u => phi ϱ L w u ^ 2)) u| ≤ cRho ϱ / w := by
  have hw0 : (0 : ℝ) < w := by linarith
  have hφ := phi_contDiff hϱ hw0 hwL
  have hφd : Differentiable ℝ (phi ϱ L w) := hφ.differentiable (by norm_num)
  have hφ'c : ContDiff ℝ 2 (deriv (phi ϱ L w)) := deriv_phi_contDiff hϱ hw0 hwL
  have hφ'd : Differentiable ℝ (deriv (phi ϱ L w)) := hφ'c.differentiable (by norm_num)
  have hφ'cont : Continuous (deriv (phi ϱ L w)) := hφ'c.continuous
  have hφ''cont : Continuous (deriv (deriv (phi ϱ L w))) := hφ'c.continuous_deriv (by norm_num)
  have hφcs := phi_hasCompactSupport hϱ (L := L) hw0
  have hφ'cs : HasCompactSupport (deriv (phi ϱ L w)) := hφcs.deriv
  have hφ''cs : HasCompactSupport (deriv (deriv (phi ϱ L w))) := hφ'cs.deriv
  have hsq1 : deriv (fun v => phi ϱ L w v ^ 2)
      = fun v => 2 * phi ϱ L w v * deriv (phi ϱ L w) v := by
    funext v
    have hd : HasDerivAt (phi ϱ L w) (deriv (phi ϱ L w) v) v := (hφd v).hasDerivAt
    have hpow : HasDerivAt (fun x => phi ϱ L w x ^ 2)
        ((2 : ℕ) * phi ϱ L w v ^ (2 - 1) * deriv (phi ϱ L w) v) v := hd.pow 2
    rw [hpow.deriv]
    norm_num
  have hid : ∀ u : ℝ, deriv (deriv (fun v => phi ϱ L w v ^ 2)) u
      = 2 * deriv (phi ϱ L w) u * deriv (phi ϱ L w) u
        + 2 * phi ϱ L w u * deriv (deriv (phi ϱ L w)) u := by
    intro u
    rw [hsq1]
    have h1 : HasDerivAt (fun v => 2 * phi ϱ L w v) (2 * deriv (phi ϱ L w) u) u :=
      (hφd u).hasDerivAt.const_mul 2
    have h2 : HasDerivAt (deriv (phi ϱ L w)) (deriv (deriv (phi ϱ L w)) u) u :=
      (hφ'd u).hasDerivAt
    have h3 : HasDerivAt (fun v => 2 * phi ϱ L w v * deriv (phi ϱ L w) v)
        (2 * deriv (phi ϱ L w) u * deriv (phi ϱ L w) u
          + 2 * phi ϱ L w u * deriv (deriv (phi ϱ L w)) u) u := by
      exact h1.mul h2
    rw [h3.deriv]
  have hint_absphi' : MeasureTheory.Integrable (fun u => |deriv (phi ϱ L w) u|) :=
    (hφ'cont.abs).integrable_of_hasCompactSupport
      (hφ'cs.comp_left (g := fun t => |t|) abs_zero)
  have hint_absphi'' : MeasureTheory.Integrable (fun u => |deriv (deriv (phi ϱ L w)) u|) :=
    (hφ''cont.abs).integrable_of_hasCompactSupport
      (hφ''cs.comp_left (g := fun t => |t|) abs_zero)
  have hφsqc : ContDiff ℝ 3 (fun v => phi ϱ L w v ^ 2) := hφ.pow 2
  have hφsq''cont : Continuous (deriv (deriv (fun v => phi ϱ L w v ^ 2))) :=
    (hφsqc.deriv' (n := 2)).continuous_deriv (by norm_num)
  have hφsqcs : HasCompactSupport (fun v => phi ϱ L w v ^ 2) :=
    hφcs.comp_left (g := fun t => t ^ 2) (by norm_num)
  have hφsq''cs : HasCompactSupport (deriv (deriv (fun v => phi ϱ L w v ^ 2))) :=
    hφsqcs.deriv.deriv
  have hint_lhs : MeasureTheory.Integrable
      (fun u => |deriv (deriv (fun v => phi ϱ L w v ^ 2)) u|) :=
    (hφsq''cont.abs).integrable_of_hasCompactSupport
      (hφsq''cs.comp_left (g := fun t => |t|) abs_zero)
  have hmaj : MeasureTheory.Integrable
      (fun u => 2 * (supDeriv ϱ / w) * |deriv (phi ϱ L w) u|
        + 2 * |deriv (deriv (phi ϱ L w)) u|) :=
    (hint_absphi'.const_mul _).add (hint_absphi''.const_mul 2)
  calc ∫ u, |deriv (deriv (fun u => phi ϱ L w u ^ 2)) u|
      ≤ ∫ u, (2 * (supDeriv ϱ / w) * |deriv (phi ϱ L w) u|
          + 2 * |deriv (deriv (phi ϱ L w)) u|) := by
        refine MeasureTheory.integral_mono hint_lhs hmaj fun u => ?_
        rw [hid u]
        have hsup := abs_deriv_phi_le hϱ hw0 hwL u
        have h1 : |2 * deriv (phi ϱ L w) u * deriv (phi ϱ L w) u|
            ≤ 2 * (supDeriv ϱ / w) * |deriv (phi ϱ L w) u| := by
          rw [abs_mul, abs_mul]
          rw [show |(2 : ℝ)| = 2 by norm_num]
          have habs0 : (0 : ℝ) ≤ |deriv (phi ϱ L w) u| := abs_nonneg _
          have := mul_le_mul_of_nonneg_right hsup habs0
          nlinarith
        have h2 : |2 * phi ϱ L w u * deriv (deriv (phi ϱ L w)) u|
            ≤ 2 * |deriv (deriv (phi ϱ L w)) u| := by
          rw [abs_mul, abs_mul]
          rw [show |(2 : ℝ)| = 2 by norm_num]
          have hφ01 : |phi ϱ L w u| ≤ 1 := by
            rw [abs_of_nonneg (phi_nonneg hϱ u)]
            exact phi_le_one hϱ u
          have habs0 : (0 : ℝ) ≤ |deriv (deriv (phi ϱ L w)) u| := abs_nonneg _
          nlinarith
        exact le_trans (abs_add_le _ _) (add_le_add h1 h2)
    _ = 2 * (supDeriv ϱ / w) * (∫ u, |deriv (phi ϱ L w) u|)
        + 2 * ∫ u, |deriv (deriv (phi ϱ L w)) u| := by
        rw [MeasureTheory.integral_add (hint_absphi'.const_mul _) (hint_absphi''.const_mul 2),
          MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    _ = 2 * (supDeriv ϱ / w) * 2 + 2 * (2 * l1Deriv2 ϱ / w) := by
        rw [integral_abs_deriv_phi hϱ hw0 hwL, integral_abs_deriv2_phi hϱ hw0 hwL]
    _ = cRho ϱ / w := by
        rw [cRho_eq]
        field_simp
        ring

/-- [eq:phinorms]: "`c_ϱ (≥ 4)`". -/
theorem four_le_cRho (hϱ : TaperProfile ϱ) : 4 ≤ cRho ϱ := by
  have hl1 := l1Deriv2_nonneg ϱ
  have hftc : ∫ y in (0 : ℝ)..1, deriv ϱ y = 1 := by
    rw [intervalIntegral.integral_deriv_eq_sub (fun x _ => rho_differentiable hϱ x)
      ((derivRho_continuous hϱ).intervalIntegrable _ _)]
    rw [hϱ.eq_one 1 le_rfl, hϱ.eq_zero 0 le_rfl]
    ring
  have hone : (1 : ℝ) ≤ supDeriv ϱ := by
    have hle : ∫ y in (0 : ℝ)..1, deriv ϱ y ≤ ∫ y in (0 : ℝ)..1, supDeriv ϱ := by
      refine intervalIntegral.integral_mono_on (by norm_num)
        ((derivRho_continuous hϱ).intervalIntegrable _ _) intervalIntegrable_const
        fun x _ => ?_
      exact le_trans (le_abs_self _) (abs_derivRho_le hϱ x)
    rw [hftc] at hle
    simpa using hle
  rw [cRho_eq]
  linarith

theorem two_mul_l1Deriv2_le_cRho (hϱ : TaperProfile ϱ) : 2 * l1Deriv2 ϱ ≤ cRho ϱ := by
  have hl1 := l1Deriv2_nonneg ϱ
  have hsup := supDeriv_nonneg hϱ
  rw [cRho_eq]
  linarith

theorem C1_eq (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    C1 ϱ L w = 2 * l1Deriv2 ϱ / w := integral_abs_deriv2_phi hϱ hw hwL

/-- "Finally `C₁ ≤ 2‖ϱ''‖₁` as `w ≥ 1`" [prop:tail proof, last lines]. -/
theorem C1_le (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 2 * w ≤ L) :
    C1 ϱ L w ≤ 2 * l1Deriv2 ϱ := by
  rw [C1_eq hϱ (by linarith) hwL]
  have := l1Deriv2_nonneg ϱ
  exact div_le_self (by linarith) hw

end Norms

/-! ### [eq:abdef]: "`1 − 2w/L ≤ b ≤ a ≤ 1`" -/

section AB
variable {ϱ : ℝ → ℝ} {L w : ℝ}

private lemma L_pos (hw : 0 < w) (hwL : 2 * w ≤ L) : (0 : ℝ) < L := by linarith

private lemma integrable_phi_pow (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L)
    {n : ℕ} (hn : 0 < n) :
    Integrable (fun u => phi ϱ L w u ^ n) :=
  ((phi_continuous hϱ hw hwL).pow n).integrable_of_hasCompactSupport
    ((phi_hasCompactSupport hϱ hw).comp_left (g := (· ^ n)) (by simp [zero_pow hn.ne']))

theorem bConst_le_aConst (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    bConst ϱ L w ≤ aConst ϱ L w := by
  have hL := L_pos hw hwL
  unfold bConst aConst
  have hmono : ∫ u : ℝ, phi ϱ L w u ^ 4 ≤ ∫ u : ℝ, phi ϱ L w u ^ 2 := by
    refine MeasureTheory.integral_mono (integrable_phi_pow hϱ hw hwL (by norm_num))
      (integrable_phi_pow hϱ hw hwL (by norm_num)) fun u => ?_
    have h0 := phi_nonneg hϱ (L := L) (w := w) u
    have h1 := phi_le_one hϱ (L := L) (w := w) u
    have hp2 : phi ϱ L w u ^ 2 ≤ 1 := pow_le_one₀ h0 h1
    have hp2n : (0 : ℝ) ≤ phi ϱ L w u ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hp2 hp2n]
  exact mul_le_mul_of_nonneg_left hmono (by positivity)

theorem aConst_le_one (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    aConst ϱ L w ≤ 1 := by
  have hL := L_pos hw hwL
  unfold aConst
  have hsupp : ∀ u ∉ Icc (-(L / 2)) (L / 2), phi ϱ L w u ^ 2 = 0 := by
    intro u hu
    have : phi ϱ L w u = 0 := by
      apply phi_eq_zero hϱ hw
      rw [mem_Icc, not_and_or, not_le, not_le] at hu
      rcases hu with h | h
      · calc L / 2 ≤ -u := by linarith
          _ ≤ |u| := neg_le_abs u
      · calc L / 2 ≤ u := by linarith
          _ ≤ |u| := le_abs_self u
    rw [this]
    ring
  have heq : ∫ u : ℝ, phi ϱ L w u ^ 2 = ∫ u in Icc (-(L / 2)) (L / 2), phi ϱ L w u ^ 2 :=
    (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hsupp).symm
  have hle : ∫ u in Icc (-(L / 2)) (L / 2), phi ϱ L w u ^ 2
      ≤ ∫ u in Icc (-(L / 2)) (L / 2), (1 : ℝ) := by
    refine MeasureTheory.setIntegral_mono_on
      ((integrable_phi_pow hϱ hw hwL (by norm_num)).integrableOn)
      (MeasureTheory.integrableOn_const (by simp)) measurableSet_Icc fun u _ => ?_
    have h0 := phi_nonneg hϱ (L := L) (w := w) u
    have h1 := phi_le_one hϱ (L := L) (w := w) u
    nlinarith
  have hvol : ∫ u in Icc (-(L / 2)) (L / 2), (1 : ℝ) = L := by
    rw [MeasureTheory.setIntegral_const]
    rw [MeasureTheory.measureReal_def, Real.volume_Icc]
    rw [ENNReal.toReal_ofReal (by linarith)]
    rw [smul_eq_mul, mul_one]
    ring
  calc L⁻¹ * ∫ u : ℝ, phi ϱ L w u ^ 2 ≤ L⁻¹ * L := by
        rw [heq]
        exact mul_le_mul_of_nonneg_left (le_trans hle (le_of_eq hvol)) (by positivity)
    _ = 1 := inv_mul_cancel₀ hL.ne'

theorem one_sub_le_bConst (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    1 - 2 * w / L ≤ bConst ϱ L w := by
  have hL := L_pos hw hwL
  unfold bConst
  have hplateau : ∫ u in Icc (-(L / 2 - w)) (L / 2 - w), phi ϱ L w u ^ 4
      = ∫ u in Icc (-(L / 2 - w)) (L / 2 - w), (1 : ℝ) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun u hu => ?_
    have h1 : phi ϱ L w u = 1 := by
      apply phi_eq_one hϱ hw
      rw [mem_Icc] at hu
      rw [abs_le]
      exact ⟨hu.1, hu.2⟩
    rw [h1]
    ring
  have hvol : ∫ u in Icc (-(L / 2 - w)) (L / 2 - w), (1 : ℝ) = L - 2 * w := by
    rw [MeasureTheory.setIntegral_const]
    rw [MeasureTheory.measureReal_def, Real.volume_Icc]
    rw [ENNReal.toReal_ofReal (by linarith)]
    rw [smul_eq_mul, mul_one]
    ring
  have hle : ∫ u in Icc (-(L / 2 - w)) (L / 2 - w), phi ϱ L w u ^ 4
      ≤ ∫ u : ℝ, phi ϱ L w u ^ 4 := by
    refine MeasureTheory.setIntegral_le_integral (integrable_phi_pow hϱ hw hwL (by norm_num)) ?_
    filter_upwards with u
    have h0 := phi_nonneg hϱ (L := L) (w := w) u
    positivity
  have hkey : L - 2 * w ≤ ∫ u : ℝ, phi ϱ L w u ^ 4 := by
    rw [← hvol, ← hplateau]
    exact hle
  calc 1 - 2 * w / L = L⁻¹ * (L - 2 * w) := by field_simp
    _ ≤ L⁻¹ * ∫ u : ℝ, phi ϱ L w u ^ 4 := mul_le_mul_of_nonneg_left hkey (by positivity)

theorem bConst_nonneg (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    0 ≤ bConst ϱ L w := by
  unfold bConst
  have h : (0 : ℝ) ≤ ∫ u : ℝ, phi ϱ L w u ^ 4 := by
    refine MeasureTheory.integral_nonneg fun u => ?_
    have h0 := phi_nonneg hϱ (L := L) (w := w) u
    positivity
  have hL := L_pos hw hwL
  positivity

end AB


end Taper

end Zeta23
