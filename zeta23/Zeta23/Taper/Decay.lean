/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — Taper/Decay.lean.  Two sections, `GBounds` and `Psi`.
Names and statements here are used by the umbrella Zeta23/Taper.lean (and the Params layer)
and by downstream files.
Canonical text: the paper, §2.2 [subsec:family].  See Zeta23/Taper.lean header for conventions:
generic parameters (ϱ : ℝ → ℝ) (L w : ℝ); paper's side condition is 1 ≤ w ≤ L/8 [eq:wrange];
each lemma carries the minimal hypothesis it needs.
-/
import Mathlib
import Zeta23.Taper.Norms
import Zeta23.Taper.Strip

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform

namespace Zeta23

namespace Taper

/-! ### [eq:gbounds]: "`(L − 2w − |y|)₊ ≤ g(y) ≤ A_φ(y) ≤ (L − |y|)₊`" -/

section GBounds

variable {ϱ : ℝ → ℝ} {L w : ℝ}

/-! Helpers on the autocorrelation `(v ⋆ v)(y) := ∫ v(u) v(u+y) du` [eq:PhigA] of a real function:
evenness (translation invariance of Lebesgue measure), the interval-overlap length
`|[−M,M] ∩ ([−M,M] − y)| = (2M − |y|)₊`, the two comparison bounds, vanishing for `|y| ≥ 2M`,
and continuity in `y` (parametric integral over the compact support). -/

theorem autocorr_even' (v : ℝ → ℝ) (y : ℝ) : Params.autocorr v (-y) = Params.autocorr v y := by
  unfold Params.autocorr
  rw [← integral_add_right_eq_self (fun u => v u * v (u + -y)) y]
  congr 1
  funext u
  rw [show u + y + -y = u by ring, mul_comm]

/-- `|[−M, M] ∩ ([−M, M] − y)| = max (2M − |y|) 0`. -/
theorem volume_Icc_inter_shift (M y : ℝ) :
    (volume (Icc (-M) M ∩ Icc (-M - y) (M - y))).toReal = max (2 * M - |y|) 0 := by
  rw [Icc_inter_Icc, Real.volume_Icc, ENNReal.toReal_ofReal']
  congr 1
  rcases le_total 0 y with h | h
  · rw [abs_of_nonneg h, max_eq_left (by linarith), min_eq_right (by linarith)]; ring
  · rw [abs_of_nonpos h, max_eq_right (by linarith), min_eq_left (by linarith)]; ring

theorem integrable_indicator_Icc_inter (M y : ℝ) :
    Integrable ((Icc (-M) M ∩ Icc (-M - y) (M - y)).indicator (1 : ℝ → ℝ)) := by
  rw [Icc_inter_Icc]
  exact (integrable_indicator_iff measurableSet_Icc).mpr
    ((integrableOn_const_iff).mpr (Or.inr (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)))

/-- Upper comparison: `0 ≤ v ≤ 1` and `v = 0` off `(−M, M)` ⟹ `(v⋆v)(y) ≤ (2M − |y|)₊`. -/
theorem autocorr_le_of_support (v : ℝ → ℝ) {M : ℝ} (h0 : ∀ u, 0 ≤ v u) (h1 : ∀ u, v u ≤ 1)
    (hz : ∀ u, M ≤ |u| → v u = 0) (y : ℝ) :
    Params.autocorr v y ≤ max (2 * M - |y|) 0 := by
  unfold Params.autocorr
  set S := Icc (-M) M ∩ Icc (-M - y) (M - y) with hS
  have hSm : MeasurableSet S := measurableSet_Icc.inter measurableSet_Icc
  have hle : ∀ u, v u * v (u + y) ≤ S.indicator 1 u := by
    intro u
    by_cases hu : u ∈ S
    · rw [indicator_of_mem hu, Pi.one_apply]
      exact mul_le_one₀ (h1 u) (h0 _) (h1 _)
    · rw [indicator_of_notMem hu]
      simp only [hS, mem_inter_iff, mem_Icc, not_and_or, not_le] at hu
      rcases hu with (hu | hu) | (hu | hu)
      · rw [hz u (by linarith [neg_le_abs u]), zero_mul]
      · rw [hz u (by linarith [le_abs_self u]), zero_mul]
      · rw [hz (u + y) (by linarith [neg_le_abs (u + y)]), mul_zero]
      · rw [hz (u + y) (by linarith [le_abs_self (u + y)]), mul_zero]
  calc ∫ u, v u * v (u + y) ≤ ∫ u, S.indicator 1 u :=
        integral_mono_of_nonneg (ae_of_all _ fun u => mul_nonneg (h0 _) (h0 _))
          (integrable_indicator_Icc_inter M y) (ae_of_all _ hle)
    _ = (volume S).toReal := integral_indicator_one hSm
    _ = max (2 * M - |y|) 0 := volume_Icc_inter_shift M y

/-- Lower comparison: `0 ≤ v`, `v = 1` on `[−M, M]`, integrand integrable ⟹ `(2M − |y|)₊ ≤ (v⋆v)(y)`. -/
theorem le_autocorr_of_plateau (v : ℝ → ℝ) {M : ℝ} (h0 : ∀ u, 0 ≤ v u)
    (hp : ∀ u, |u| ≤ M → v u = 1) {y : ℝ} (hint : Integrable fun u => v u * v (u + y)) :
    max (2 * M - |y|) 0 ≤ Params.autocorr v y := by
  unfold Params.autocorr
  set S := Icc (-M) M ∩ Icc (-M - y) (M - y) with hS
  have hSm : MeasurableSet S := measurableSet_Icc.inter measurableSet_Icc
  have hle : ∀ u, S.indicator 1 u ≤ v u * v (u + y) := by
    intro u
    by_cases hu : u ∈ S
    · rw [indicator_of_mem hu, Pi.one_apply]
      simp only [hS, mem_inter_iff, mem_Icc] at hu
      rw [hp u (abs_le.mpr ⟨hu.1.1, hu.1.2⟩), hp (u + y) (abs_le.mpr ⟨by linarith, by linarith⟩),
        mul_one]
    · rw [indicator_of_notMem hu]
      exact mul_nonneg (h0 _) (h0 _)
  calc max (2 * M - |y|) 0 = (volume S).toReal := (volume_Icc_inter_shift M y).symm
    _ = ∫ u, S.indicator 1 u := (integral_indicator_one hSm).symm
    _ ≤ ∫ u, v u * v (u + y) :=
        integral_mono_of_nonneg (ae_of_all _ fun u => Set.indicator_nonneg (fun _ _ => zero_le_one) u)
          hint (ae_of_all _ hle)

/-- `v = 0` off `(−M, M)` and `|y| ≥ 2M` ⟹ `(v⋆v)(y) = 0` (the supports of `v` and `v(·+y)` are disjoint). -/
theorem autocorr_eq_zero_of_support (v : ℝ → ℝ) {M : ℝ} (hz : ∀ u, M ≤ |u| → v u = 0) {y : ℝ}
    (hy : 2 * M ≤ |y|) : Params.autocorr v y = 0 := by
  unfold Params.autocorr
  have : (fun u => v u * v (u + y)) = fun _ => 0 := by
    funext u
    by_cases hu : M ≤ |u|
    · rw [hz u hu, zero_mul]
    · rw [hz (u + y) ?_, mul_zero]
      have := abs_sub_abs_le_abs_sub y (-u)
      rw [abs_neg, sub_neg_eq_add, add_comm] at this
      have hu := not_le.mp hu
      linarith
  rw [this, integral_zero]

/-- Continuity of `y ↦ (v⋆v)(y)` for continuous `v` vanishing off `(−M, M)`. -/
theorem autocorr_continuous_of_support (v : ℝ → ℝ) {M : ℝ} (hc : Continuous v)
    (hz : ∀ u, M ≤ |u| → v u = 0) : Continuous (Params.autocorr v) := by
  have : Params.autocorr v = fun y => ∫ u in Icc (-M) M, v u * v (u + y) := by
    funext y
    unfold Params.autocorr
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro u hu
    rw [hz u ?_, zero_mul]
    simp only [mem_Icc, not_and_or, not_le] at hu
    rcases hu with hu | hu
    · linarith [neg_le_abs u]
    · linarith [le_abs_self u]
  rw [this]
  exact continuous_parametric_integral_of_continuous
    (by fun_prop : Continuous (fun p : ℝ × ℝ => v p.2 * v (p.2 + p.1))) isCompact_Icc

/-! The taper instances: `A_φ = φ ⋆ φ` (support `[−L/2, L/2]`, `0 ≤ φ ≤ 1`) and `g = φ² ⋆ φ²`
(plateau `φ² = 1` on `[−L/2+w, L/2−w]`). -/

theorem phi_sq_eq_zero (hϱ : TaperProfile ϱ) (hw : 0 < w) (u : ℝ) (hu : L / 2 ≤ |u|) :
    phi ϱ L w u ^ 2 = 0 := by
  rw [phi_eq_zero hϱ hw hu, zero_pow two_ne_zero]

theorem integrable_phi_mul_shift (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (y : ℝ) :
    Integrable fun u => phi ϱ L w u * phi ϱ L w (u + y) := by
  have hc := phi_continuous hϱ hw hwL
  refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
  refine HasCompactSupport.intro (K := Icc (-(L / 2)) (L / 2)) isCompact_Icc fun u hu => ?_
  rw [phi_eq_zero hϱ hw ?_, zero_mul]
  simp only [mem_Icc, not_and_or, not_le] at hu
  rcases hu with hu | hu
  · linarith [neg_le_abs u]
  · linarith [le_abs_self u]

theorem integrable_phi_sq_mul_shift (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (y : ℝ) :
    Integrable fun u => phi ϱ L w u ^ 2 * phi ϱ L w (u + y) ^ 2 := by
  have hc := phi_continuous hϱ hw hwL
  refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
  refine HasCompactSupport.intro (K := Icc (-(L / 2)) (L / 2)) isCompact_Icc fun u hu => ?_
  rw [phi_sq_eq_zero hϱ hw u ?_, zero_mul]
  simp only [mem_Icc, not_and_or, not_le] at hu
  rcases hu with hu | hu
  · linarith [neg_le_abs u]
  · linarith [le_abs_self u]

/-- "`g` and `A_φ` are even". -/
theorem Aphi_even (y : ℝ) : Aphi ϱ L w (-y) = Aphi ϱ L w y :=
  autocorr_even' _ y

theorem g_even (y : ℝ) : g ϱ L w (-y) = g ϱ L w y :=
  autocorr_even' _ y

theorem g_ge (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (y : ℝ) :
    max (L - 2 * w - |y|) 0 ≤ g ϱ L w y := by
  have h := le_autocorr_of_plateau (fun u => phi ϱ L w u ^ 2) (M := L / 2 - w)
    (fun u => sq_nonneg _) (fun u hu => by rw [phi_eq_one hϱ hw hu, one_pow])
    (integrable_phi_sq_mul_shift hϱ hw hwL y)
  rw [show 2 * (L / 2 - w) = L - 2 * w by ring] at h
  exact h

theorem g_le_Aphi (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (y : ℝ) :
    g ϱ L w y ≤ Aphi ϱ L w y := by
  unfold g Aphi Params.autocorr
  refine integral_mono_of_nonneg (ae_of_all _ fun u => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (integrable_phi_mul_shift hϱ hw hwL y) (ae_of_all _ fun u => ?_)
  have h0 := phi_nonneg (L := L) (w := w) hϱ
  have h1 := phi_le_one (L := L) (w := w) hϱ
  exact mul_le_mul (pow_le_of_le_one (h0 _) (h1 _) two_ne_zero)
    (pow_le_of_le_one (h0 _) (h1 _) two_ne_zero) (sq_nonneg _) (h0 _)

theorem Aphi_le (hϱ : TaperProfile ϱ) (hw : 0 < w) (_hwL : 2 * w ≤ L) (y : ℝ) :
    Aphi ϱ L w y ≤ max (L - |y|) 0 := by
  have h := autocorr_le_of_support (phi ϱ L w) (M := L / 2) (phi_nonneg hϱ) (phi_le_one hϱ)
    (fun u hu => phi_eq_zero hϱ hw hu) y
  rw [show 2 * (L / 2) = L by ring] at h
  exact h

theorem g_nonneg (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (y : ℝ) :
    0 ≤ g ϱ L w y :=
  le_trans (le_max_right _ _) (g_ge hϱ hw hwL y)

theorem Aphi_nonneg (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (y : ℝ) :
    0 ≤ Aphi ϱ L w y :=
  le_trans (g_nonneg hϱ hw hwL y) (g_le_Aphi hϱ hw hwL y)

/-- `g(y) = 0` for `|y| ≥ L` (so `Σ_n a_n² g(log n)` runs over `n ≤ X = e^L` only). -/
theorem g_eq_zero (hϱ : TaperProfile ϱ) (hw : 0 < w) (_hwL : 2 * w ≤ L) {y : ℝ}
    (hy : L ≤ |y|) : g ϱ L w y = 0 :=
  autocorr_eq_zero_of_support (fun u => phi ϱ L w u ^ 2) (M := L / 2)
    (fun u hu => phi_sq_eq_zero hϱ hw u hu) (by linarith)

/-- "(and `A_φ(L) = 0`)" [prop:trace, P-part]; more generally `A_φ(y) = 0` for `|y| ≥ L`. -/
theorem Aphi_eq_zero (hϱ : TaperProfile ϱ) (hw : 0 < w) (_hwL : 2 * w ≤ L) {y : ℝ}
    (hy : L ≤ |y|) : Aphi ϱ L w y = 0 :=
  autocorr_eq_zero_of_support (phi ϱ L w) (M := L / 2) (fun u hu => phi_eq_zero hϱ hw hu)
    (by linarith)

theorem g_continuous (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Continuous (g ϱ L w) :=
  autocorr_continuous_of_support (fun u => phi ϱ L w u ^ 2) (M := L / 2) ((phi_continuous hϱ hw hwL).pow 2)
    (fun u hu => phi_sq_eq_zero hϱ hw u hu)

theorem Aphi_continuous (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Continuous (Aphi ϱ L w) :=
  autocorr_continuous_of_support (phi ϱ L w) (M := L / 2) (phi_continuous hϱ hw hwL)
    (fun _ hu => phi_eq_zero hϱ hw hu)

end GBounds

/-! ### [eq:psidef]: "`max(|φ̂(r)|, |Φ(r)|) ≤ ψ(r) := min(L, 2/|r|, c_ϱ/(w r²))`"
We give the three bounds separately (division-free) and then the `ψ` form. -/

section Psi 
variable {ϱ : ℝ → ℝ} {L w : ℝ}

/-! #### Helpers: first-order [eq:hfbound], and the ℂ-valued φ² -/

/-- [eq:hfbound], first order (one integration by parts): supp f ⊆ [−Λ, Λ], f ∈ C_c¹ ⇒
‖h_f(z)‖ · ‖z‖ ≤ e^{|Im z| Λ} ‖f'‖₁. (Companion of Zeta23.norm_paperFT_mul_sq_le.) -/
theorem norm_paperFT_mul_le {f : ℝ → ℂ} {Λ : ℝ} (hf : ContDiff ℝ 1 f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ) (z : ℂ) :
    ‖paperFT f z‖ * ‖z‖ ≤ Real.exp (|z.im| * Λ) * ∫ u, ‖deriv f u‖ := by
  have hcs : HasCompactSupport f := hasCompactSupport_of_support_subset_abs hsupp
  have hts := tsupport_subset_of_support_subset_abs hsupp
  have hsupp1 : ∀ u, deriv f u ≠ 0 → |u| ≤ Λ := by
    intro u hu
    have : u ∈ tsupport f := support_deriv_subset (Function.mem_support.mpr hu)
    exact abs_le.mpr (hts this)
  have hint : Integrable (deriv f) :=
    (hf.continuous_deriv le_rfl).integrable_of_hasCompactSupport hcs.deriv
  have := norm_paperFT_le hint hsupp1 z
  rw [paperFT_deriv hf hcs, norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul,
    mul_comm] at this
  exact this

/-- The ℂ-valued φ² used in Φ := (φ²)^ is C² with support in [−L/2, L/2]. -/
theorem phiSqC_contDiff (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ContDiff ℝ 2 (fun u => (((phi ϱ L w u) ^ 2 : ℝ) : ℂ)) := by
  have h : ContDiff ℝ 2 (fun u => (phi ϱ L w u) ^ 2) :=
    ((phi_contDiff hϱ hw hwL).of_le (by norm_num)).pow 2
  exact ofRealCLM.contDiff.comp h

theorem phiSqC_support (hϱ : TaperProfile ϱ) (hw : 0 < w) (u : ℝ)
    (hu : (((phi ϱ L w u) ^ 2 : ℝ) : ℂ) ≠ 0) : |u| ≤ L / 2 := by
  by_contra h
  apply hu
  rw [phi_eq_zero hϱ hw (le_of_lt (not_le.mp h))]
  simp

theorem deriv_phiSqC (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    deriv (fun u => (((phi ϱ L w u) ^ 2 : ℝ) : ℂ))
      = fun u => ((deriv (fun u => phi ϱ L w u ^ 2) u : ℝ) : ℂ) :=
  deriv_ofReal_comp (((phi_contDiff hϱ hw hwL).differentiable (by norm_num)).pow 2)

theorem deriv_deriv_phiSqC (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    deriv (deriv (fun u => (((phi ϱ L w u) ^ 2 : ℝ) : ℂ)))
      = fun u => ((deriv (deriv (fun u => phi ϱ L w u ^ 2)) u : ℝ) : ℂ) := by
  have h2 : ContDiff ℝ 2 (fun u => (phi ϱ L w u) ^ 2) :=
    ((phi_contDiff hϱ hw hwL).of_le (by norm_num)).pow 2
  rw [deriv_phiSqC hϱ hw hwL]
  exact deriv_ofReal_comp ((h2.deriv' (n := 1)).differentiable (by norm_num))

/-- ∫ φ² ≤ L. -/
theorem integral_phi_sq_le (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ∫ u, (phi ϱ L w u) ^ 2 ≤ L := by
  refine le_trans (integral_mono_of_nonneg (Eventually.of_forall fun u => sq_nonneg _)
    (phi_integrable hϱ hw hwL) (Eventually.of_forall fun u => ?_)) (integral_phi_le hϱ hw hwL)
  have h0 := phi_nonneg hϱ (L := L) (w := w) u
  have h1 := phi_le_one hϱ (L := L) (w := w) u
  nlinarith

theorem abs_phiHatR_le_norm (r : ℝ) : |phiHatR ϱ L w r| ≤ ‖phiHat ϱ L w r‖ :=
  Complex.abs_re_le_norm _

theorem abs_PhiR_le_norm (r : ℝ) : |PhiR ϱ L w r| ≤ ‖Phi ϱ L w r‖ :=
  Complex.abs_re_le_norm _

theorem abs_phiHatR_le_L (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (r : ℝ) :
    |phiHatR ϱ L w r| ≤ L := by
  refine (abs_phiHatR_le_norm r).trans ?_
  have h := norm_phiHat_le hϱ hw hwL (r : ℂ)
  simpa using h

theorem abs_phiHatR_mul_abs_le (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (r : ℝ) :
    |phiHatR ϱ L w r| * |r| ≤ 2 := by
  have h := norm_paperFT_mul_le ((phiC_contDiff hϱ hw hwL).of_le (by norm_num))
    (phiC_support hϱ hw) (r : ℂ)
  rw [deriv_ofReal_comp ((phi_contDiff hϱ hw hwL).differentiable (by norm_num))] at h
  simp only [Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_im, abs_zero, zero_mul,
    Real.exp_zero, one_mul, integral_abs_deriv_phi hϱ hw hwL] at h
  calc |phiHatR ϱ L w r| * |r| ≤ ‖phiHat ϱ L w r‖ * |r| :=
        mul_le_mul_of_nonneg_right (abs_phiHatR_le_norm r) (abs_nonneg r)
    _ ≤ 2 := h

theorem abs_phiHatR_mul_sq_le (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 2 * w ≤ L) (r : ℝ) :
    |phiHatR ϱ L w r| * r ^ 2 ≤ cRho ϱ / w := by
  have hw0 : 0 < w := by linarith
  have h := norm_phiHat_mul_sq_le hϱ hw0 hwL (r : ℂ)
  simp only [Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_im, abs_zero, zero_mul,
    Real.exp_zero, one_mul, sq_abs] at h
  calc |phiHatR ϱ L w r| * r ^ 2 ≤ ‖phiHat ϱ L w r‖ * r ^ 2 :=
        mul_le_mul_of_nonneg_right (abs_phiHatR_le_norm r) (sq_nonneg r)
    _ ≤ C1 ϱ L w := h
    _ = 2 * l1Deriv2 ϱ / w := C1_eq hϱ hw0 hwL
    _ ≤ cRho ϱ / w := div_le_div_of_nonneg_right (two_mul_l1Deriv2_le_cRho hϱ) hw0.le

theorem abs_PhiR_le_L (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (r : ℝ) :
    |PhiR ϱ L w r| ≤ L := by
  refine (abs_PhiR_le_norm r).trans ?_
  have hint : Integrable (fun u => (((phi ϱ L w u) ^ 2 : ℝ) : ℂ)) :=
    ((phiSqC_contDiff hϱ hw hwL).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_of_support_subset_abs (phiSqC_support hϱ hw)))
  have h := norm_paperFT_le hint (phiSqC_support hϱ hw) (r : ℂ)
  simp only [Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_im, abs_zero, zero_mul,
    Real.exp_zero, one_mul] at h
  refine h.trans ?_
  calc ∫ u, |phi ϱ L w u ^ 2| = ∫ u, phi ϱ L w u ^ 2 := by
        congr 1 with u; exact abs_of_nonneg (sq_nonneg _)
    _ ≤ L := integral_phi_sq_le hϱ hw hwL

theorem abs_PhiR_mul_abs_le (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (r : ℝ) :
    |PhiR ϱ L w r| * |r| ≤ 2 := by
  have h := norm_paperFT_mul_le ((phiSqC_contDiff hϱ hw hwL).of_le (by norm_num))
    (phiSqC_support hϱ hw) (r : ℂ)
  rw [deriv_phiSqC hϱ hw hwL] at h
  simp only [Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_im, abs_zero, zero_mul,
    Real.exp_zero, one_mul, integral_abs_deriv_phi_sq hϱ hw hwL] at h
  calc |PhiR ϱ L w r| * |r| ≤ ‖Phi ϱ L w r‖ * |r| :=
        mul_le_mul_of_nonneg_right (abs_PhiR_le_norm r) (abs_nonneg r)
    _ ≤ 2 := h

theorem abs_PhiR_mul_sq_le (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 2 * w ≤ L) (r : ℝ) :
    |PhiR ϱ L w r| * r ^ 2 ≤ cRho ϱ / w := by
  have hw0 : 0 < w := by linarith
  have h := norm_paperFT_mul_sq_le (phiSqC_contDiff hϱ hw0 hwL) (phiSqC_support hϱ hw0) (r : ℂ)
  rw [deriv_deriv_phiSqC hϱ hw0 hwL] at h
  simp only [Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_im, abs_zero, zero_mul,
    Real.exp_zero, one_mul, sq_abs] at h
  calc |PhiR ϱ L w r| * r ^ 2 ≤ ‖Phi ϱ L w r‖ * r ^ 2 :=
        mul_le_mul_of_nonneg_right (abs_PhiR_le_norm r) (sq_nonneg r)
    _ ≤ ∫ u, |deriv (deriv fun u => phi ϱ L w u ^ 2) u| := h
    _ ≤ cRho ϱ / w := integral_abs_deriv2_phi_sq_le hϱ hw hwL

/-- [eq:psidef] abstractly: the three bounds `|F| ≤ L`, `|F|·|r| ≤ 2`, `|F|·r² ≤ c_ϱ/w` give `|F| ≤ ψ`. -/
theorem abs_le_psi_of_bounds (hw : 0 < w) {F : ℝ → ℝ} (h0 : ∀ r, |F r| ≤ L)
    (h1 : ∀ r, |F r| * |r| ≤ 2) (h2 : ∀ r, |F r| * r ^ 2 ≤ cRho ϱ / w) (r : ℝ) :
    |F r| ≤ psi ϱ L w r := by
  unfold psi
  split_ifs with hr
  · exact h0 r
  · have hra : 0 < |r| := abs_pos.mpr hr
    refine le_min (h0 r) (le_min ?_ ?_)
    · rw [le_div_iff₀ hra]; exact h1 r
    · rw [le_div_iff₀ (by positivity), show w * r ^ 2 = r ^ 2 * w by ring, ← mul_assoc,
        ← le_div_iff₀ hw]
      exact h2 r

theorem abs_phiHatR_le_psi (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 2 * w ≤ L) (r : ℝ) :
    |phiHatR ϱ L w r| ≤ psi ϱ L w r :=
  abs_le_psi_of_bounds (by linarith) (abs_phiHatR_le_L hϱ (by linarith) hwL)
    (abs_phiHatR_mul_abs_le hϱ (by linarith) hwL) (abs_phiHatR_mul_sq_le hϱ hw hwL) r

theorem abs_PhiR_le_psi (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 2 * w ≤ L) (r : ℝ) :
    |PhiR ϱ L w r| ≤ psi ϱ L w r :=
  abs_le_psi_of_bounds (by linarith) (abs_PhiR_le_L hϱ (by linarith) hwL)
    (abs_PhiR_mul_abs_le hϱ (by linarith) hwL) (abs_PhiR_mul_sq_le hϱ hw hwL) r

theorem psi_nonneg (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 2 * w ≤ L) (r : ℝ) :
    0 ≤ psi ϱ L w r := by
  have hL : 0 ≤ L := by linarith
  have hc : 0 ≤ cRho ϱ := le_trans (by norm_num) (four_le_cRho hϱ)
  unfold psi
  split_ifs with hr
  · exact hL
  · exact le_min hL (le_min (by positivity) (by positivity))

theorem psi_even (r : ℝ) : psi ϱ L w (-r) = psi ϱ L w r := by
  simp [psi]

theorem psi_le_L (_hϱ : TaperProfile ϱ) (_hw : 1 ≤ w) (_hwL : 2 * w ≤ L) (r : ℝ) :
    psi ϱ L w r ≤ L := by
  unfold psi
  split_ifs with hr
  · exact le_rfl
  · exact min_le_left _ _

theorem psi_mul_abs_le (_hϱ : TaperProfile ϱ) (_hw : 1 ≤ w) (_hwL : 2 * w ≤ L) (r : ℝ) :
    psi ϱ L w r * |r| ≤ 2 := by
  unfold psi
  split_ifs with hr
  · simp [hr]
  · have hra : 0 < |r| := abs_pos.mpr hr
    rw [← le_div_iff₀ hra]
    exact (min_le_right _ _).trans (min_le_left _ _)

theorem psi_mul_sq_le (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (_hwL : 2 * w ≤ L) (r : ℝ) :
    psi ϱ L w r * r ^ 2 ≤ cRho ϱ / w := by
  have hw0 : 0 < w := by linarith
  have hc : 0 ≤ cRho ϱ := le_trans (by norm_num) (four_le_cRho hϱ)
  unfold psi
  split_ifs with hr
  · simp [hr]; positivity
  · have hr2 : 0 < r ^ 2 := by positivity
    rw [← le_div_iff₀ hr2, div_div, mul_comm]
    exact (min_le_right _ _).trans (min_le_right _ _)

/-! #### Measurability / integrability of ψ -/

theorem psi_abs (r : ℝ) : psi ϱ L w |r| = psi ϱ L w r := by
  unfold psi
  simp only [abs_eq_zero, abs_abs, sq_abs]

theorem psi_measurable : Measurable (psi ϱ L w) := by
  have h1 : Measurable (fun r : ℝ => min L (min (2 / |r|) (cRho ϱ / (w * r ^ 2)))) :=
    measurable_const.min ((measurable_const.div continuous_abs.measurable).min
      (measurable_const.div (measurable_const.mul (measurable_id.pow_const 2))))
  have : psi ϱ L w = Set.piecewise {(0:ℝ)} (fun _ => L) (fun r => min L (min (2 / |r|) (cRho ϱ / (w * r ^ 2)))) := by
    funext r
    unfold psi
    by_cases hr : r = 0
    · rw [if_pos hr, Set.piecewise_eq_of_mem _ _ _ (by simp [hr])]
    · rw [if_neg hr, Set.piecewise_eq_of_notMem _ _ _ (by simp [hr])]
  rw [this]
  exact Measurable.piecewise (measurableSet_singleton 0) measurable_const h1

/-- For r > 0: ψ(r) ≤ (c_ϱ/w) · r^{−2} (rpow form). -/
theorem psi_le_rpow_neg_two (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 2 * w ≤ L) {r : ℝ}
    (hr : 0 < r) : psi ϱ L w r ≤ cRho ϱ / w * r ^ (-2:ℝ) := by
  have h := psi_mul_sq_le hϱ hw hwL r
  rw [Real.rpow_neg hr.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast,
    ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  exact h

/-- The common integrable plateau majorant: `a` on [−1,1] and `b·|r|⁻²` outside (ψ: a = L, b = c_ϱ/w;
r²-moments: a = 4, b = C²).  ∫ = 2a + 2b. -/
private noncomputable def plateauMaj (a b : ℝ) (r : ℝ) : ℝ :=
  (Icc (-1:ℝ) 1).indicator (fun _ => a) r
    + b * ((Ioi (1:ℝ)).indicator (fun x => x ^ (-2:ℝ)) r + (Ioi (1:ℝ)).indicator (fun x => x ^ (-2:ℝ)) (-r))

private theorem tail_indicator_integrable :
    Integrable ((Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ))) :=
  (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).integrable_indicator measurableSet_Ioi

private theorem plateauMaj_integrable (a b : ℝ) : Integrable (plateauMaj a b) :=
  ((integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))).add
    ((tail_indicator_integrable.add tail_indicator_integrable.comp_neg).const_mul _)

private theorem integral_plateauMaj (a b : ℝ) : ∫ r, plateauMaj a b r = 2 * a + 2 * b := by
  have h1 : Integrable ((Icc (-1:ℝ) 1).indicator (fun _ => a)) :=
    (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))
  have h2 := tail_indicator_integrable
  have h3 : Integrable (fun r => (Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) (-r)) := h2.comp_neg
  have e1 : ∫ r, (Icc (-1:ℝ) 1).indicator (fun _ => a) r = 2 * a := by
    rw [integral_indicator measurableSet_Icc, setIntegral_const, measureReal_def,
      Real.volume_Icc, ENNReal.toReal_ofReal (by norm_num), smul_eq_mul]
    norm_num
  have e2 : ∫ r, (Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) r = 1 := by
    rw [integral_indicator measurableSet_Ioi, integral_Ioi_rpow_of_lt (by norm_num) one_pos]
    norm_num
  have e3 : ∫ r, (Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) (-r) = 1 := by
    rw [MeasureTheory.integral_neg_eq_self ((Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ))) volume]
    exact e2
  have h23 : Integrable (fun r => (Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) r
      + (Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) (-r)) := h2.add h3
  unfold plateauMaj
  calc ∫ r, ((Icc (-1:ℝ) 1).indicator (fun _ => a) r
        + b * ((Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) r
          + (Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) (-r)))
      = (∫ r, (Icc (-1:ℝ) 1).indicator (fun _ => a) r)
        + ∫ r, b * ((Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) r
          + (Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) (-r)) :=
        integral_add h1 (h23.const_mul _)
    _ = 2 * a + b * ((∫ r, (Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) r)
          + ∫ r, (Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) (-r)) := by
        rw [e1, integral_const_mul]
        congr 2
        exact integral_add h2 h3
    _ = 2 * a + 2 * b := by rw [e2, e3]; ring

/-- The integrable majorant of ψ: L on [−1,1] and (c_ϱ/w)|r|⁻² outside. -/
private noncomputable abbrev psiMaj (ϱ : ℝ → ℝ) (L w : ℝ) : ℝ → ℝ := plateauMaj L (cRho ϱ / w)

private theorem psiMaj_integrable : Integrable (psiMaj ϱ L w) := plateauMaj_integrable _ _

private theorem psi_le_psiMaj (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 2 * w ≤ L) (r : ℝ) :
    psi ϱ L w r ≤ psiMaj ϱ L w r := by
  have hw0 : 0 < w := by linarith
  have hc : 0 ≤ cRho ϱ := le_trans (by norm_num) (four_le_cRho hϱ)
  have hind : ∀ s : ℝ, 0 ≤ (Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) s := fun s =>
    Set.indicator_nonneg (fun x hx => Real.rpow_nonneg (le_trans zero_le_one (le_of_lt hx)) _) _
  unfold psiMaj plateauMaj
  by_cases h : r ∈ Icc (-1:ℝ) 1
  · rw [Set.indicator_of_mem h]
    have := psi_le_L hϱ hw hwL r
    nlinarith [hind r, hind (-r), div_nonneg hc hw0.le]
  · rw [Set.indicator_of_notMem h, zero_add]
    rw [mem_Icc, not_and_or, not_le, not_le] at h
    rcases h with h | h
    · -- r < -1
      have hr : 0 < -r := by linarith
      rw [Set.indicator_of_notMem (show r ∉ Ioi (1:ℝ) by simp; linarith),
        Set.indicator_of_mem (show -r ∈ Ioi (1:ℝ) by simp; linarith), zero_add]
      have := psi_le_rpow_neg_two hϱ hw hwL hr
      rw [← psi_abs, abs_of_neg (by linarith)]
      exact this
    · -- 1 < r
      have hr : 0 < r := by linarith
      rw [Set.indicator_of_mem (show r ∈ Ioi (1:ℝ) from h),
        Set.indicator_of_notMem (show -r ∉ Ioi (1:ℝ) by simp; linarith), add_zero]
      exact psi_le_rpow_neg_two hϱ hw hwL hr

/-- φ̂_ℝ is continuous (paperFT of an integrable function, at real arguments; dominated
convergence with the bound ‖φ‖). Auxiliary version for this file; Zeta23/Taper/Fourier.lean
(downstream) carries phiHatR_continuous. -/
theorem continuous_paperFT_ofReal {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (fun r : ℝ => paperFT f r) := by
  unfold paperFT
  refine continuous_of_dominated (bound := fun u => ‖f u‖) (fun r => ?_) (fun r => ?_)
    hf.norm ?_
  · exact hf.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop))
  · refine Eventually.of_forall fun u => ?_
    rw [norm_mul, norm_cexp_I_mul]
    simp
  · exact Eventually.of_forall fun u => by fun_prop

theorem continuous_phiHatR_aux (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Continuous (phiHatR ϱ L w) := by
  unfold phiHatR phiHat
  exact Complex.continuous_re.comp
    (continuous_paperFT_ofReal (phi_integrable hϱ hw hwL).ofReal)

theorem continuous_PhiR_aux (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Continuous (PhiR ϱ L w) := by
  unfold PhiR Phi
  refine Complex.continuous_re.comp (continuous_paperFT_ofReal ?_)
  exact (phiSqC_contDiff hϱ hw hwL).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_of_support_subset_abs (phiSqC_support hϱ hw))

/-! ### [eq:psiints].  We record upper bounds — every downstream citation of [eq:psiints] in §5 is
"≪ log L" or "≤ 8L".  (Paper: "a direct computation (split at |r| = 2/L and |r| = c_ϱ/2w; note
c_ϱ L/4w ≥ 1 by [eq:wrange]) gives Ψ₀ = 4 + 2 log(c_ϱ L/4w), ∫ψ²|r| = 8 + 8 log(c_ϱ L/4w),
∫ψ² ≤ 8L".) -/

/-- Constants for [eq:psiints]: A := 2/L ≤ B := c_ϱ/(2w) ("note c_ϱ L/4w ≥ 1 by
[eq:wrange]"), B/A = c_ϱ L/(4w). -/
private theorem psiints_consts (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    0 < 2 / L ∧ 0 < cRho ϱ / (2 * w) ∧ 2 / L ≤ cRho ϱ / (2 * w) ∧
    (cRho ϱ / (2 * w)) / (2 / L) = cRho ϱ * L / (4 * w) := by
  have hc := four_le_cRho hϱ
  have hL : 0 < L := by linarith
  have hw0 : 0 < w := by linarith
  refine ⟨by positivity, by positivity, ?_, ?_⟩
  · rw [div_le_div_iff₀ hL (by positivity)]; nlinarith
  · field_simp; ring

/-- On (0, ∞), ψ is dominated by the three-piece majorant L·1_{(0,A]} + (2/r)·1_{(A,B]} +
(c_ϱ/w) r⁻²·1_{(B,∞)} (in fact with equality; ≤ is all we use). -/
private theorem indicator_psi_le (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) (r : ℝ) :
    (Ioi (0:ℝ)).indicator (psi ϱ L w) r
      ≤ (Ioc 0 (2 / L)).indicator (fun _ => L) r
        + (Ioc (2 / L) (cRho ϱ / (2 * w))).indicator (fun x => 2 * x⁻¹) r
        + (Ioi (cRho ϱ / (2 * w))).indicator (fun x => cRho ϱ / w * x ^ (-2:ℝ)) r := by
  obtain ⟨hA, hB, hAB, -⟩ := psiints_consts hϱ hw hwL
  have hwL' : 2 * w ≤ L := by linarith
  by_cases hr : r ∈ Ioi (0:ℝ)
  · have hr0 : 0 < r := hr
    rw [indicator_of_mem hr]
    by_cases h1 : r ≤ 2 / L
    · rw [indicator_of_mem (show r ∈ Ioc 0 (2 / L) from ⟨hr0, h1⟩),
        indicator_of_notMem (show r ∉ Ioc (2 / L) (cRho ϱ / (2 * w)) from
          fun h => not_lt.mpr h1 h.1),
        indicator_of_notMem (show r ∉ Ioi (cRho ϱ / (2 * w)) from
          fun h => not_lt.mpr (h1.trans hAB) h), add_zero, add_zero]
      exact psi_le_L hϱ hw hwL' r
    · rw [not_le] at h1
      by_cases h2 : r ≤ cRho ϱ / (2 * w)
      · rw [indicator_of_notMem (show r ∉ Ioc 0 (2 / L) from fun h => not_le.mpr h1 h.2),
          indicator_of_mem (show r ∈ Ioc (2 / L) (cRho ϱ / (2 * w)) from ⟨h1, h2⟩),
          indicator_of_notMem (show r ∉ Ioi (cRho ϱ / (2 * w)) from fun h => not_lt.mpr h2 h),
          zero_add, add_zero]
        have := psi_mul_abs_le hϱ hw hwL' r
        rw [abs_of_pos hr0] at this
        rw [← div_eq_mul_inv, le_div_iff₀ hr0]
        exact this
      · rw [not_le] at h2
        rw [indicator_of_notMem (show r ∉ Ioc 0 (2 / L) from fun h => not_le.mpr h1 h.2),
          indicator_of_notMem (show r ∉ Ioc (2 / L) (cRho ϱ / (2 * w)) from
            fun h => not_le.mpr h2 h.2),
          indicator_of_mem (show r ∈ Ioi (cRho ϱ / (2 * w)) from h2), zero_add, zero_add]
        exact psi_le_rpow_neg_two hϱ hw hwL' hr0
  · rw [indicator_of_notMem hr]
    have hr0 : r ≤ 0 := not_lt.mp hr
    rw [indicator_of_notMem (show r ∉ Ioc 0 (2 / L) from fun h => hr h.1),
      indicator_of_notMem (show r ∉ Ioc (2 / L) (cRho ϱ / (2 * w)) from
        fun h => hr (lt_trans hA h.1)),
      indicator_of_notMem (show r ∉ Ioi (cRho ϱ / (2 * w)) from fun h => hr (lt_trans hB h)),
      add_zero, add_zero]

/-- [eq:psiints]: Ψ₀ := ∫₀^∞ ψ(r) dr ≤ 4 + 2 log(c_ϱ L/(4w)) (paper: "="). -/
theorem integral_psi_Ioi_le (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    ∫ r in Ioi 0, psi ϱ L w r ≤ 4 + 2 * Real.log (cRho ϱ * L / (4 * w)) := by
  obtain ⟨hA, hB, hAB, hBA⟩ := psiints_consts hϱ hw hwL
  have hwL' : 2 * w ≤ L := by linarith
  have hL : 0 < L := by linarith
  have hw0 : 0 < w := by linarith
  have hc0 : 0 < cRho ϱ := lt_of_lt_of_le (by norm_num) (four_le_cRho hϱ)
  set A := 2 / L with hAdef
  set B := cRho ϱ / (2 * w) with hBdef
  -- integrability of the three pieces
  have i1 : IntegrableOn (fun _ : ℝ => L) (Ioc 0 A) := integrableOn_const (by simp)
  have i2 : IntegrableOn (fun x : ℝ => 2 * x⁻¹) (Ioc A B) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Ioc_subset_Icc_self
    exact continuousOn_const.mul
      ((continuousOn_inv₀).mono fun x hx => ne_of_gt (lt_of_lt_of_le hA hx.1))
  have i3 : IntegrableOn (fun x : ℝ => cRho ϱ / w * x ^ (-2:ℝ)) (Ioi B) :=
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
  have e3 : ∫ r, (Ioi B).indicator (fun x => cRho ϱ / w * x ^ (-2:ℝ)) r = 2 := by
    rw [integral_indicator measurableSet_Ioi, integral_const_mul,
      integral_Ioi_rpow_of_lt (by norm_num) hB]
    norm_num
    rw [Real.rpow_neg_one, hBdef]
    field_simp
  have I12 : Integrable (fun r => (Ioc 0 A).indicator (fun _ => L) r
      + (Ioc A B).indicator (fun x => 2 * x⁻¹) r) := I1.add I2
  calc ∫ r in Ioi 0, psi ϱ L w r
      = ∫ r, (Ioi (0:ℝ)).indicator (psi ϱ L w) r := (integral_indicator measurableSet_Ioi).symm
    _ ≤ ∫ r, ((Ioc 0 A).indicator (fun _ => L) r
          + (Ioc A B).indicator (fun x => 2 * x⁻¹) r
          + (Ioi B).indicator (fun x => cRho ϱ / w * x ^ (-2:ℝ)) r) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun r => ?_) ((I1.add I2).add I3)
          (Eventually.of_forall fun r => indicator_psi_le hϱ hw hwL r)
        exact Set.indicator_nonneg (fun x _ => psi_nonneg hϱ hw hwL' x) _
    _ = (∫ r, ((Ioc 0 A).indicator (fun _ => L) r + (Ioc A B).indicator (fun x => 2 * x⁻¹) r))
          + ∫ r, (Ioi B).indicator (fun x => cRho ϱ / w * x ^ (-2:ℝ)) r := integral_add I12 I3
    _ = ((∫ r, (Ioc 0 A).indicator (fun _ => L) r) + ∫ r, (Ioc A B).indicator (fun x => 2 * x⁻¹) r)
          + ∫ r, (Ioi B).indicator (fun x => cRho ϱ / w * x ^ (-2:ℝ)) r := by
        rw [integral_add I1 I2]
    _ = 2 + 2 * Real.log (B / A) + 2 := by rw [e1, e2, e3]
    _ = 4 + 2 * Real.log (cRho ϱ * L / (4 * w)) := by rw [hBA]; ring

/-- [eq:psiints]: ∫_ℝ ψ(r)²|r| dr ≤ 8 + 8 log(c_ϱ L/(4w)) (paper: "="): split (0,2/L],
(2/L, c/2w], (c/2w, ∞): ∫₀^∞ ψ² r ≤ L²(2/L)²/2 + 4 log(cL/4w) + (c/w)²/(2(c/2w)²) = 2 + 4 log + 2. -/
theorem integral_psi_sq_mul_abs_le (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    ∫ r, psi ϱ L w r ^ 2 * |r| ≤ 8 + 8 * Real.log (cRho ϱ * L / (4 * w)) := by
  obtain ⟨hA, hB, hAB, hBA⟩ := psiints_consts hϱ hw hwL
  have hwL' : 2 * w ≤ L := by linarith
  have hL : 0 < L := by linarith
  have hw0 : 0 < w := by linarith
  have hc0 : 0 < cRho ϱ := lt_of_lt_of_le (by norm_num) (four_le_cRho hϱ)
  set A := 2 / L with hAdef
  set B := cRho ϱ / (2 * w) with hBdef
  have hred : ∫ r, psi ϱ L w r ^ 2 * |r| = 2 * ∫ r in Ioi 0, psi ϱ L w r ^ 2 * r := by
    have h := integral_comp_abs (f := fun x => psi ϱ L w x ^ 2 * x)
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
  have i3 : IntegrableOn (fun x : ℝ => (cRho ϱ / w) ^ 2 * x ^ (-3:ℝ)) (Ioi B) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hB).const_mul _
  have I1 := i1.integrable_indicator measurableSet_Ioc
  have I2 := i2.integrable_indicator measurableSet_Ioc
  have I3 := i3.integrable_indicator measurableSet_Ioi
  have I12 : Integrable (fun r => (Ioc 0 A).indicator (fun x : ℝ => L ^ 2 * x) r
      + (Ioc A B).indicator (fun x : ℝ => 4 * x⁻¹) r) := I1.add I2
  have I123 : Integrable (fun r => (Ioc 0 A).indicator (fun x : ℝ => L ^ 2 * x) r
      + (Ioc A B).indicator (fun x : ℝ => 4 * x⁻¹) r
      + (Ioi B).indicator (fun x : ℝ => (cRho ϱ / w) ^ 2 * x ^ (-3:ℝ)) r) := I12.add I3
  have hpt : ∀ r, (Ioi (0:ℝ)).indicator (fun x => psi ϱ L w x ^ 2 * x) r
      ≤ (Ioc 0 A).indicator (fun x : ℝ => L ^ 2 * x) r
        + (Ioc A B).indicator (fun x : ℝ => 4 * x⁻¹) r
        + (Ioi B).indicator (fun x : ℝ => (cRho ϱ / w) ^ 2 * x ^ (-3:ℝ)) r := by
    intro r
    have h0 := psi_nonneg hϱ hw hwL' r
    by_cases hr : 0 < r
    · rw [indicator_of_mem (show r ∈ Ioi (0:ℝ) from hr)]
      by_cases h1 : r ≤ A
      · rw [indicator_of_mem (show r ∈ Ioc 0 A from ⟨hr, h1⟩),
          indicator_of_notMem (show r ∉ Ioc A B from fun h => not_lt.mpr h1 h.1),
          indicator_of_notMem (show r ∉ Ioi B from fun h => not_lt.mpr (h1.trans hAB) h),
          add_zero, add_zero]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 (psi_le_L hϱ hw hwL' r) 2) hr.le
      · have h1' : A < r := not_le.mp h1
        by_cases h2 : r ≤ B
        · rw [indicator_of_notMem (show r ∉ Ioc 0 A from fun h => h1 h.2),
            indicator_of_mem (show r ∈ Ioc A B from ⟨h1', h2⟩),
            indicator_of_notMem (show r ∉ Ioi B from fun h => not_lt.mpr h2 h), zero_add, add_zero]
          have h := psi_mul_abs_le hϱ hw hwL' r
          rw [abs_of_pos hr] at h
          -- ψ² r = (ψ r)·ψ ≤ 2 ψ ≤ 2 · (2/r)
          have h3 : psi ϱ L w r ≤ 2 * r⁻¹ := by
            rw [← div_eq_mul_inv, le_div_iff₀ hr]; exact h
          calc psi ϱ L w r ^ 2 * r = (psi ϱ L w r * r) * psi ϱ L w r := by ring
            _ ≤ 2 * (2 * r⁻¹) := mul_le_mul h h3 h0 (by norm_num)
            _ = 4 * r⁻¹ := by ring
        · have h2' : B < r := not_le.mp h2
          rw [indicator_of_notMem (show r ∉ Ioc 0 A from fun h => h1 h.2),
            indicator_of_notMem (show r ∉ Ioc A B from fun h => h2 h.2),
            indicator_of_mem (show r ∈ Ioi B from h2'), zero_add, zero_add]
          have h := psi_le_rpow_neg_two hϱ hw hwL' hr
          have hcw : 0 ≤ cRho ϱ / w * r ^ (-2:ℝ) := by positivity
          calc psi ϱ L w r ^ 2 * r ≤ (cRho ϱ / w * r ^ (-2:ℝ)) ^ 2 * r := by
                exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h 2) hr.le
            _ = (cRho ϱ / w) ^ 2 * r ^ (-3:ℝ) := by
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
  have e3 : ∫ r, (Ioi B).indicator (fun x : ℝ => (cRho ϱ / w) ^ 2 * x ^ (-3:ℝ)) r = 2 := by
    rw [integral_indicator measurableSet_Ioi, integral_const_mul,
      integral_Ioi_rpow_of_lt (by norm_num) hB]
    norm_num
    rw [hBdef]
    field_simp
  calc 2 * ∫ r in Ioi 0, psi ϱ L w r ^ 2 * r
      = 2 * ∫ r, (Ioi (0:ℝ)).indicator (fun x => psi ϱ L w x ^ 2 * x) r := by
        rw [integral_indicator measurableSet_Ioi]
    _ ≤ 2 * ∫ r, ((Ioc 0 A).indicator (fun x : ℝ => L ^ 2 * x) r
          + (Ioc A B).indicator (fun x : ℝ => 4 * x⁻¹) r
          + (Ioi B).indicator (fun x : ℝ => (cRho ϱ / w) ^ 2 * x ^ (-3:ℝ)) r) :=
        mul_le_mul_of_nonneg_left (integral_mono_of_nonneg (Eventually.of_forall fun r =>
            Set.indicator_nonneg (fun x hx => mul_nonneg (sq_nonneg _) (le_of_lt hx)) _) I123
          (Eventually.of_forall hpt)) (by norm_num)
    _ = 2 * (2 + 4 * Real.log (B / A) + 2) := by rw [integral_add I12 I3, integral_add I1 I2, e1, e2, e3]
    _ = 8 + 8 * Real.log (cRho ϱ * L / (4 * w)) := by rw [hBA]; ring

/-- [eq:psiints]: "∫_ℝ ψ² ≤ 8L". Uses only ψ ≤ min(L, 2/|r|):
∫ = 2∫₀^∞ ≤ 2(∫₀^{2/L} L² + ∫_{2/L}^∞ 4r⁻²) = 2(2L+2L). -/
theorem integral_psi_sq_le (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    ∫ r, psi ϱ L w r ^ 2 ≤ 8 * L := by
  obtain ⟨hA, -, -, -⟩ := psiints_consts hϱ hw hwL
  have hwL' : 2 * w ≤ L := by linarith
  have hL : 0 < L := by linarith
  set A := 2 / L with hAdef
  have hred : ∫ r, psi ϱ L w r ^ 2 = 2 * ∫ r in Ioi 0, psi ϱ L w r ^ 2 := by
    have h := integral_comp_abs (f := fun x => psi ϱ L w x ^ 2)
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
  have hpt : ∀ r, (Ioi (0:ℝ)).indicator (fun x => psi ϱ L w x ^ 2) r
      ≤ (Ioc 0 A).indicator (fun _ : ℝ => L ^ 2) r + (Ioi A).indicator (fun x : ℝ => 4 * x ^ (-2:ℝ)) r := by
    intro r
    have h0 := psi_nonneg hϱ hw hwL' r
    by_cases hr : 0 < r
    · rw [indicator_of_mem (show r ∈ Ioi (0:ℝ) from hr)]
      by_cases h1 : r ≤ A
      · rw [indicator_of_mem (show r ∈ Ioc 0 A from ⟨hr, h1⟩),
          indicator_of_notMem (show r ∉ Ioi A from fun h => not_lt.mpr h1 h), add_zero]
        exact pow_le_pow_left₀ h0 (psi_le_L hϱ hw hwL' r) 2
      · have h1' : A < r := not_le.mp h1
        rw [indicator_of_notMem (show r ∉ Ioc 0 A from fun h => h1 h.2),
          indicator_of_mem (show r ∈ Ioi A from h1'), zero_add]
        have h := psi_mul_abs_le hϱ hw hwL' r
        rw [abs_of_pos hr] at h
        have h2 : psi ϱ L w r ≤ 2 * r⁻¹ := by
          rw [← div_eq_mul_inv, le_div_iff₀ hr]; exact h
        calc psi ϱ L w r ^ 2 ≤ (2 * r⁻¹) ^ 2 := pow_le_pow_left₀ h0 h2 2
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
  calc 2 * ∫ r in Ioi 0, psi ϱ L w r ^ 2
      = 2 * ∫ r, (Ioi (0:ℝ)).indicator (fun x => psi ϱ L w x ^ 2) r := by
        rw [integral_indicator measurableSet_Ioi]
    _ ≤ 2 * ∫ r, ((Ioc 0 A).indicator (fun _ : ℝ => L ^ 2) r
          + (Ioi A).indicator (fun x : ℝ => 4 * x ^ (-2:ℝ)) r) :=
        mul_le_mul_of_nonneg_left (integral_mono_of_nonneg
          (Eventually.of_forall fun r => Set.indicator_nonneg (fun x _ => sq_nonneg _) _) I12
          (Eventually.of_forall hpt)) (by norm_num)
    _ = 2 * (2 * L + 2 * L) := by rw [integral_add I1 I2, e1, e2]
    _ = 8 * L := by ring

theorem psi_integrable (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    Integrable (psi ϱ L w) := by
  have hwL' : 2 * w ≤ L := by linarith
  refine (psiMaj_integrable (ϱ := ϱ) (L := L) (w := w)).mono'
    psi_measurable.aestronglyMeasurable (Eventually.of_forall fun r => ?_)
  rw [Real.norm_of_nonneg (psi_nonneg hϱ hw hwL' r)]
  exact psi_le_psiMaj hϱ hw hwL' r

theorem psi_sq_integrable (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    Integrable (fun r => psi ϱ L w r ^ 2) := by
  have hwL' : 2 * w ≤ L := by linarith
  refine ((psi_integrable hϱ hw hwL).const_mul L).mono'
    (psi_measurable.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun r => ?_)
  have h0 := psi_nonneg hϱ hw hwL' r
  have h1 := psi_le_L hϱ hw hwL' r
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  nlinarith

theorem psi_sq_mul_abs_integrable (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    Integrable (fun r => psi ϱ L w r ^ 2 * |r|) := by
  have hwL' : 2 * w ≤ L := by linarith
  refine ((psi_integrable hϱ hw hwL).const_mul 2).mono'
    ((psi_measurable.pow_const 2).mul continuous_abs.measurable).aestronglyMeasurable
    (Eventually.of_forall fun r => ?_)
  have h0 := psi_nonneg hϱ hw hwL' r
  have h1 := psi_mul_abs_le hϱ hw hwL' r
  rw [Real.norm_of_nonneg (by positivity)]
  nlinarith

/-! #### Generic moment bounds from |F| ≤ ψ-type information -/

/-- If |F| ≤ ψ pointwise then ∫ F²|r| ≤ ∫ ψ²|r| ≤ 8 + 8 log(c_ϱ L/4w). -/
private theorem integral_sq_mul_abs_le_of_le_psi (hϱ : TaperProfile ϱ) (hw : 1 ≤ w)
    (hwL : 8 * w ≤ L) {F : ℝ → ℝ} (hF : ∀ r, |F r| ≤ psi ϱ L w r) :
    ∫ r, F r ^ 2 * |r| ≤ 8 + 8 * Real.log (cRho ϱ * L / (4 * w)) := by
  refine le_trans (integral_mono_of_nonneg (Eventually.of_forall fun r => by positivity)
    (psi_sq_mul_abs_integrable hϱ hw hwL) (Eventually.of_forall fun r => ?_))
    (integral_psi_sq_mul_abs_le hϱ hw hwL)
  have h : F r ^ 2 ≤ psi ϱ L w r ^ 2 := by
    rw [← sq_abs (F r)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hF r) 2
  exact mul_le_mul_of_nonneg_right h (abs_nonneg r)

/-- The integrable majorant for the r²-moments: 4 on [−1,1] and C²|r|⁻² outside. -/
private noncomputable abbrev momMaj (C : ℝ) : ℝ → ℝ := plateauMaj 4 (C ^ 2)

private theorem momMaj_integrable (C : ℝ) : Integrable (momMaj C) := plateauMaj_integrable _ _

private theorem integral_momMaj (C : ℝ) : ∫ r, momMaj C r = 8 + 2 * C ^ 2 := by
  rw [integral_plateauMaj]; ring

/-- Pointwise: |F(r)|·|r| ≤ 2 and |F(r)|·r² ≤ C give F(r)² r² ≤ momMaj C r. -/
private theorem sq_mul_sq_le_momMaj {F : ℝ → ℝ} {C : ℝ} (_hC : 0 ≤ C)
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
  unfold momMaj plateauMaj
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

private theorem integrable_sq_mul_sq_of_bounds {F : ℝ → ℝ} {C : ℝ} (hFc : Continuous F)
    (hC : 0 ≤ C) (h1 : ∀ r, |F r| * |r| ≤ 2) (h2 : ∀ r, |F r| * r ^ 2 ≤ C) :
    Integrable (fun r => F r ^ 2 * r ^ 2) := by
  refine (momMaj_integrable C).mono' (by fun_prop) (Eventually.of_forall fun r => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact sq_mul_sq_le_momMaj hC h1 h2 r

private theorem integral_sq_mul_sq_le_of_bounds {F : ℝ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (h1 : ∀ r, |F r| * |r| ≤ 2) (h2 : ∀ r, |F r| * r ^ 2 ≤ C) :
    ∫ r, F r ^ 2 * r ^ 2 ≤ 8 + 2 * C ^ 2 := by
  rw [← integral_momMaj C]
  exact integral_mono_of_nonneg (Eventually.of_forall fun r => by positivity)
    (momMaj_integrable C) (Eventually.of_forall fun r => sq_mul_sq_le_momMaj hC h1 h2 r)

/-- Consequence packaged for [prop:trace]/[prop:mumu]: ∫ φ̂(r)² |r| dr ≤ 8 + 8 log(c_ϱ L/4w). -/
theorem integral_phiHatR_sq_mul_abs_le (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    ∫ r, phiHatR ϱ L w r ^ 2 * |r| ≤ 8 + 8 * Real.log (cRho ϱ * L / (4 * w)) :=
  integral_sq_mul_abs_le_of_le_psi hϱ hw hwL
    (fun r => abs_phiHatR_le_psi hϱ hw (by linarith) r)

theorem integral_PhiR_sq_mul_abs_le (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    ∫ x, PhiR ϱ L w x ^ 2 * |x| ≤ 8 + 8 * Real.log (cRho ϱ * L / (4 * w)) :=
  integral_sq_mul_abs_le_of_le_psi hϱ hw hwL
    (fun r => abs_PhiR_le_psi hϱ hw (by linarith) r)

/-- Used for [prop:trace] (μ/Π tails): `φ̂(r)² r²` is integrable … -/
theorem integrable_phiHatR_sq_mul_sq (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    Integrable (fun r => phiHatR ϱ L w r ^ 2 * r ^ 2) := by
  have hw0 : 0 < w := by linarith
  have hwL' : 2 * w ≤ L := by linarith
  exact integrable_sq_mul_sq_of_bounds (continuous_phiHatR_aux hϱ hw0 hwL')
    (div_nonneg (le_trans (by norm_num) (four_le_cRho hϱ)) hw0.le)
    (abs_phiHatR_mul_abs_le hϱ hw0 hwL') (abs_phiHatR_mul_sq_le hϱ hw hwL')

/-- … and `∫ φ̂(r)² r² dr ≤ 8 + 2 (c_ϱ/w)²` (from [eq:psidef]: `φ̂² r² ≤ 4` on `|r| ≤ 1`,
`≤ (c_ϱ/w)² r⁻²` on `|r| > 1`). -/
theorem integral_phiHatR_sq_mul_sq_le (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    ∫ r, phiHatR ϱ L w r ^ 2 * r ^ 2 ≤ 8 + 2 * (cRho ϱ / w) ^ 2 := by
  have hw0 : 0 < w := by linarith
  have hwL' : 2 * w ≤ L := by linarith
  exact integral_sq_mul_sq_le_of_bounds
    (div_nonneg (le_trans (by norm_num) (four_le_cRho hϱ)) hw0.le)
    (abs_phiHatR_mul_abs_le hϱ hw0 hwL') (abs_phiHatR_mul_sq_le hϱ hw hwL')

/-- Φ analogue (used for [prop:mumu]): `Φ(x)² x²` integrable … -/
theorem integrable_PhiR_sq_mul_sq (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    Integrable (fun x => PhiR ϱ L w x ^ 2 * x ^ 2) := by
  have hw0 : 0 < w := by linarith
  have hwL' : 2 * w ≤ L := by linarith
  exact integrable_sq_mul_sq_of_bounds (continuous_PhiR_aux hϱ hw0 hwL')
    (div_nonneg (le_trans (by norm_num) (four_le_cRho hϱ)) hw0.le)
    (abs_PhiR_mul_abs_le hϱ hw0 hwL') (abs_PhiR_mul_sq_le hϱ hw hwL')

/-- … and `∫ Φ(x)² x² dx ≤ 8 + 2 (c_ϱ/w)²` (same ψ route as for φ̂). -/
theorem integral_PhiR_sq_mul_sq_le (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    ∫ x, PhiR ϱ L w x ^ 2 * x ^ 2 ≤ 8 + 2 * (cRho ϱ / w) ^ 2 := by
  have hw0 : 0 < w := by linarith
  have hwL' : 2 * w ≤ L := by linarith
  exact integral_sq_mul_sq_le_of_bounds
    (div_nonneg (le_trans (by norm_num) (four_le_cRho hϱ)) hw0.le)
    (abs_PhiR_mul_abs_le hϱ hw0 hwL') (abs_PhiR_mul_sq_le hϱ hw hwL')

end Psi


end Taper

end Zeta23
