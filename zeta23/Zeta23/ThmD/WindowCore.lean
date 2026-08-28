/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmD/WindowCore.lean — the test-family facts of §5 for an ARBITRARY admissible window
(the generic half of "BridgeD").

Paper §7.1: "Propositions 5.1–5.5 hold verbatim for any even C_c² window with the same support
and derivative norms."  We package such a window as `AdmWindow v L w c` (even, `0 ≤ v ≤ 1`,
`C²`, `supp v ⊆ [−L/2, L/2]`, `‖v'‖₁, ‖(v²)'‖₁ ≤ 2`, `‖v''‖₁, ‖(v²)''‖₁ ≤ c/w`, `c ≥ 4`,
`1 ≤ w`, `8w ≤ L`) and derive, ONCE, everything `LocalHypsCore` asks of the data
`(v̂, (v²)^, v⋆v, v²⋆v², a, b)` — by the same generic lemmas (Zeta23/Poisson/PaperFT.lean,
Zeta23/Taper/{Strip,Decay,Fourier}.lean §Generic, Zeta23/Poisson.lean) that the flat-top facade
Zeta23/Taper.lean specializes to `Taper.phi`.  The Montgomery–Taylor window `ThmD.phiD` is an
`AdmWindow` with `c = cDT` (Zeta23/ThmD/BridgeD.lean); so is the flat window with `c = cRho ϱ`.
-/
import Zeta23.Taper
import Zeta23.Poisson
import Zeta23.PrimeSideA.Basic
import Zeta23.PiFacts

noncomputable section

open Complex MeasureTheory Real Set Filter Topology

namespace Zeta23

/-- An admissible window for §5 (paper §2 test family minus the flat top; §7.1). -/
structure AdmWindow (v : ℝ → ℝ) (L w c : ℝ) : Prop where
  one_le_w : 1 ≤ w
  w8 : 8 * w ≤ L
  four_le_c : 4 ≤ c
  even : ∀ u, v (-u) = v u
  nonneg : ∀ u, 0 ≤ v u
  le_one : ∀ u, v u ≤ 1
  contDiff : ContDiff ℝ 2 v
  support : ∀ u, L / 2 ≤ |u| → v u = 0
  l1_deriv : ∫ u, |deriv v u| ≤ 2
  l1_deriv_sq : ∫ u, |deriv (fun u => v u ^ 2) u| ≤ 2
  l1_deriv2 : ∫ u, |deriv (deriv v) u| ≤ c / w
  l1_deriv2_sq : ∫ u, |deriv (deriv (fun u => v u ^ 2)) u| ≤ c / w

namespace AdmWindow

/-! ## The data attached to a window -/

section Defs
variable (v : ℝ → ℝ) (L : ℝ)

/-- `v̂` (paper Fourier convention), complex argument. -/
def vHat (z : ℂ) : ℂ := paperFT (fun u => (v u : ℂ)) z
/-- `v̂` restricted to ℝ (real-valued since `v` is real and even). -/
def vHatR (r : ℝ) : ℝ := (vHat v r).re
/-- `V := (v²)^`. -/
def VPhi (z : ℂ) : ℂ := paperFT (fun u => (((v u) ^ 2 : ℝ) : ℂ)) z
def VPhiR (r : ℝ) : ℝ := (VPhi v r).re
/-- `A_v := v ⋆ v`. -/
def Av (y : ℝ) : ℝ := Params.autocorr v y
/-- `g_v := v² ⋆ v²`. -/
def gv (y : ℝ) : ℝ := Params.autocorr (fun u => v u ^ 2) y
/-- `a := L⁻¹ ∫ v²`, `b := L⁻¹ ∫ v⁴`. -/
def av : ℝ := L⁻¹ * ∫ u, v u ^ 2
def bv : ℝ := L⁻¹ * ∫ u, v u ^ 4

/-- The abstract local data of the window (`LocalFun`). -/
def localFun : PrimeSide.LocalFun := ⟨vHatR v, VPhiR v, Av v, gv v, av v L, bv v L⟩

end Defs

variable {v : ℝ → ℝ} {L w c : ℝ}

/-! ## Elementary consequences of admissibility -/

section Basic
variable (hW : AdmWindow v L w c)
include hW

lemma w_pos : 0 < w := lt_of_lt_of_le one_pos hW.one_le_w
lemma L_pos : 0 < L := by linarith [hW.one_le_w, hW.w8]
lemma two_w_le : 2 * w ≤ L := by linarith [hW.one_le_w, hW.w8]
lemma c_nonneg : 0 ≤ c := le_trans (by norm_num) hW.four_le_c

lemma continuous : Continuous v := hW.contDiff.continuous

lemma eq_zero_of_not_mem {u : ℝ} (hu : u ∉ Icc (-(L / 2)) (L / 2)) : v u = 0 := by
  apply hW.support
  simp only [mem_Icc, not_and_or, not_le] at hu
  rcases hu with hu | hu
  · linarith [neg_le_abs u]
  · linarith [le_abs_self u]

lemma hasCompactSupport : HasCompactSupport v :=
  HasCompactSupport.intro isCompact_Icc fun _ hu => hW.eq_zero_of_not_mem hu

lemma support_subset : Function.support v ⊆ Icc (-(L / 2)) (L / 2) := fun u hu => by
  by_contra h
  exact hu (hW.eq_zero_of_not_mem h)

lemma integrable : Integrable v := hW.continuous.integrable_of_hasCompactSupport hW.hasCompactSupport

lemma sq_even (u : ℝ) : v (-u) ^ 2 = v u ^ 2 := by rw [hW.even]

lemma sq_eq_zero (u : ℝ) (hu : L / 2 ≤ |u|) : v u ^ 2 = 0 := by
  rw [hW.support u hu, zero_pow two_ne_zero]

lemma sq_hasCompactSupport : HasCompactSupport (fun u => v u ^ 2) :=
  hW.hasCompactSupport.comp_left (g := fun x : ℝ => x ^ 2) (by simp)

lemma sq_continuous : Continuous (fun u => v u ^ 2) := hW.continuous.pow 2

lemma integrable_pow {n : ℕ} (hn : 0 < n) : Integrable (fun u => v u ^ n) :=
  (hW.continuous.pow n).integrable_of_hasCompactSupport
    (hW.hasCompactSupport.comp_left (g := (· ^ n)) (by simp [zero_pow hn.ne']))

/-! #### the ℂ-valued window and its square, as inputs to the PaperFT lemmas -/

lemma vC_continuous : Continuous (fun u => (v u : ℂ)) := Complex.continuous_ofReal.comp hW.continuous

lemma vC_hasCompactSupport : HasCompactSupport (fun u => (v u : ℂ)) :=
  hW.hasCompactSupport.comp_left Complex.ofReal_zero

lemma vC_contDiff : ContDiff ℝ 2 (fun u => (v u : ℂ)) := by
  have := Complex.ofRealCLM.contDiff.comp hW.contDiff
  simpa [Function.comp_def] using this

lemma vC_supp : ∀ u, (v u : ℂ) ≠ 0 → |u| ≤ L / 2 := by
  intro u hu
  by_contra h
  exact hu (by rw [hW.support u (le_of_lt (not_le.mp h)), ofReal_zero])

lemma vSqC_continuous : Continuous (fun u => (((v u) ^ 2 : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.comp hW.sq_continuous

lemma vSqC_hasCompactSupport : HasCompactSupport (fun u => (((v u) ^ 2 : ℝ) : ℂ)) :=
  hW.hasCompactSupport.comp_left (g := fun x : ℝ => ((x ^ 2 : ℝ) : ℂ)) (by simp)

lemma vSqC_contDiff : ContDiff ℝ 2 (fun u => (((v u) ^ 2 : ℝ) : ℂ)) := by
  have := Complex.ofRealCLM.contDiff.comp (hW.contDiff.pow 2)
  simpa [Function.comp_def] using this

lemma vSqC_supp : ∀ u, (((v u) ^ 2 : ℝ) : ℂ) ≠ 0 → |u| ≤ L / 2 := by
  intro u hu
  apply hW.vC_supp u
  intro h
  apply hu
  rw [Complex.ofReal_eq_zero] at h
  simp [h]

/-! #### `∫ v ≤ L`, `∫ v² ≤ L` -/

lemma integral_le : ∫ u, v u ≤ L := by
  have hL : 0 ≤ L := hW.L_pos.le
  have hle : ∀ u, v u ≤ (Icc (-(L / 2)) (L / 2)).indicator (fun _ => (1 : ℝ)) u := by
    intro u
    by_cases hu : u ∈ Icc (-(L / 2)) (L / 2)
    · rw [indicator_of_mem hu]; exact hW.le_one u
    · rw [indicator_of_notMem hu, hW.eq_zero_of_not_mem hu]
  calc ∫ u, v u ≤ ∫ u, (Icc (-(L / 2)) (L / 2)).indicator (fun _ => (1 : ℝ)) u := by
        apply integral_mono hW.integrable _ hle
        exact (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))
    _ = L := by
        rw [integral_indicator_const _ measurableSet_Icc, measureReal_def, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith), smul_eq_mul, mul_one]
        ring

lemma sq_le_self (u : ℝ) : v u ^ 2 ≤ v u := by
  have h0 := hW.nonneg u; have h1 := hW.le_one u; nlinarith

lemma integral_sq_le : ∫ u, v u ^ 2 ≤ L :=
  le_trans (integral_mono (hW.integrable_pow two_pos) hW.integrable hW.sq_le_self) hW.integral_le

end Basic

/-! ## [eq:hfbound]-type pointwise bounds for `v̂` and `V` -/

section Bounds
variable (hW : AdmWindow v L w c)
include hW

lemma norm_vHat_le (z : ℂ) : ‖vHat v z‖ ≤ Real.exp (|z.im| * (L / 2)) * L := by
  have hint : Integrable (fun u => (v u : ℂ)) :=
    hW.vC_continuous.integrable_of_hasCompactSupport hW.vC_hasCompactSupport
  have h := norm_paperFT_le hint hW.vC_supp z
  simp only [Complex.norm_real, Real.norm_eq_abs] at h
  refine le_trans h ?_
  gcongr
  calc ∫ u, |v u| = ∫ u, v u := by congr 1 with u; exact abs_of_nonneg (hW.nonneg u)
    _ ≤ L := hW.integral_le

lemma norm_vHat_mul_sq_le (z : ℂ) :
    ‖vHat v z‖ * ‖z‖ ^ 2 ≤ Real.exp (|z.im| * (L / 2)) * ∫ u, |deriv (deriv v) u| := by
  have h := norm_paperFT_mul_sq_le hW.vC_contDiff hW.vC_supp z
  have hd1 : Differentiable ℝ v := hW.contDiff.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (deriv v) := (hW.contDiff.deriv' (n := 1)).differentiable (by norm_num)
  rw [Taper.deriv_ofReal_comp hd1, Taper.deriv_ofReal_comp hd2] at h
  simp only [Complex.norm_real, Real.norm_eq_abs] at h
  exact h

set_option linter.unusedSectionVars false in  -- `hW` is unused here but kept so that call sites can write `hW.<name>`
lemma abs_vHatR_le_norm (r : ℝ) : |vHatR v r| ≤ ‖vHat v r‖ := Complex.abs_re_le_norm _
set_option linter.unusedSectionVars false in  -- `hW` is unused here but kept so that call sites can write `hW.<name>`
lemma abs_VPhiR_le_norm (r : ℝ) : |VPhiR v r| ≤ ‖VPhi v r‖ := Complex.abs_re_le_norm _

lemma abs_vHatR_le_L (r : ℝ) : |vHatR v r| ≤ L := by
  refine (hW.abs_vHatR_le_norm r).trans ?_
  simpa using hW.norm_vHat_le (r : ℂ)

lemma abs_vHatR_mul_abs_le (r : ℝ) : |vHatR v r| * |r| ≤ 2 := by
  have h := Taper.norm_paperFT_mul_le (hW.vC_contDiff.of_le (by norm_num)) hW.vC_supp (r : ℂ)
  rw [Taper.deriv_ofReal_comp (hW.contDiff.differentiable (by norm_num))] at h
  simp only [Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_im, abs_zero, zero_mul,
    Real.exp_zero, one_mul] at h
  calc |vHatR v r| * |r| ≤ ‖vHat v r‖ * |r| :=
        mul_le_mul_of_nonneg_right (hW.abs_vHatR_le_norm r) (abs_nonneg r)
    _ ≤ ∫ u, |deriv v u| := h
    _ ≤ 2 := hW.l1_deriv

lemma abs_vHatR_mul_sq_le (r : ℝ) : |vHatR v r| * r ^ 2 ≤ c / w := by
  have h := hW.norm_vHat_mul_sq_le (r : ℂ)
  simp only [Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_im, abs_zero, zero_mul,
    Real.exp_zero, one_mul, sq_abs] at h
  calc |vHatR v r| * r ^ 2 ≤ ‖vHat v r‖ * r ^ 2 :=
        mul_le_mul_of_nonneg_right (hW.abs_vHatR_le_norm r) (sq_nonneg r)
    _ ≤ ∫ u, |deriv (deriv v) u| := h
    _ ≤ c / w := hW.l1_deriv2

lemma abs_VPhiR_le_L (r : ℝ) : |VPhiR v r| ≤ L := by
  refine (hW.abs_VPhiR_le_norm r).trans ?_
  have hint : Integrable (fun u => (((v u) ^ 2 : ℝ) : ℂ)) :=
    hW.vSqC_continuous.integrable_of_hasCompactSupport hW.vSqC_hasCompactSupport
  have h := norm_paperFT_le hint hW.vSqC_supp (r : ℂ)
  simp only [Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_im, abs_zero, zero_mul,
    Real.exp_zero, one_mul] at h
  refine h.trans ?_
  calc ∫ u, |v u ^ 2| = ∫ u, v u ^ 2 := by congr 1 with u; exact abs_of_nonneg (sq_nonneg _)
    _ ≤ L := hW.integral_sq_le

lemma abs_VPhiR_mul_abs_le (r : ℝ) : |VPhiR v r| * |r| ≤ 2 := by
  have h := Taper.norm_paperFT_mul_le (hW.vSqC_contDiff.of_le (by norm_num)) hW.vSqC_supp (r : ℂ)
  have hd1 : Differentiable ℝ (fun u => v u ^ 2) := (hW.contDiff.differentiable (by norm_num)).pow 2
  rw [Taper.deriv_ofReal_comp hd1] at h
  simp only [Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_im, abs_zero, zero_mul,
    Real.exp_zero, one_mul] at h
  calc |VPhiR v r| * |r| ≤ ‖VPhi v r‖ * |r| :=
        mul_le_mul_of_nonneg_right (hW.abs_VPhiR_le_norm r) (abs_nonneg r)
    _ ≤ ∫ u, |deriv (fun u => v u ^ 2) u| := h
    _ ≤ 2 := hW.l1_deriv_sq

lemma abs_VPhiR_mul_sq_le (r : ℝ) : |VPhiR v r| * r ^ 2 ≤ c / w := by
  have h := norm_paperFT_mul_sq_le hW.vSqC_contDiff hW.vSqC_supp (r : ℂ)
  have hd1 : Differentiable ℝ (fun u => v u ^ 2) := (hW.contDiff.differentiable (by norm_num)).pow 2
  have hd2 : Differentiable ℝ (deriv (fun u => v u ^ 2)) :=
    (((hW.contDiff.pow 2).deriv' (n := 1)).differentiable (by norm_num))
  rw [Taper.deriv_ofReal_comp hd1, Taper.deriv_ofReal_comp hd2] at h
  simp only [Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_im, abs_zero, zero_mul,
    Real.exp_zero, one_mul, sq_abs] at h
  calc |VPhiR v r| * r ^ 2 ≤ ‖VPhi v r‖ * r ^ 2 :=
        mul_le_mul_of_nonneg_right (hW.abs_VPhiR_le_norm r) (sq_nonneg r)
    _ ≤ ∫ u, |deriv (deriv fun u => v u ^ 2) u| := h
    _ ≤ c / w := hW.l1_deriv2_sq

/-- `|v̂| ≤ ψ_c` in the majorant spelling `psiA c p` (for any `p` with `p.L = L`, `p.w = w`). -/
lemma abs_vHatR_le_psiA (p : PrimeSide.Setting) (hL : p.L = L) (hw : p.w = w) (r : ℝ) :
    |vHatR v r| ≤ PrimeSide.psiA c p r := by
  unfold PrimeSide.psiA
  rw [hL, hw]
  split_ifs with hr
  · exact hW.abs_vHatR_le_L r
  · have hra : 0 < |r| := abs_pos.mpr hr
    refine le_min (hW.abs_vHatR_le_L r) (le_min ?_ ?_)
    · rw [le_div_iff₀ hra]; exact hW.abs_vHatR_mul_abs_le r
    · rw [le_div_iff₀ (by have := hW.w_pos; positivity), show w * r ^ 2 = r ^ 2 * w by ring,
        ← mul_assoc, ← le_div_iff₀ hW.w_pos]
      exact hW.abs_vHatR_mul_sq_le r

lemma abs_VPhiR_le_psiA (p : PrimeSide.Setting) (hL : p.L = L) (hw : p.w = w) (r : ℝ) :
    |VPhiR v r| ≤ PrimeSide.psiA c p r := by
  unfold PrimeSide.psiA
  rw [hL, hw]
  split_ifs with hr
  · exact hW.abs_VPhiR_le_L r
  · have hra : 0 < |r| := abs_pos.mpr hr
    refine le_min (hW.abs_VPhiR_le_L r) (le_min ?_ ?_)
    · rw [le_div_iff₀ hra]; exact hW.abs_VPhiR_mul_abs_le r
    · rw [le_div_iff₀ (by have := hW.w_pos; positivity), show w * r ^ 2 = r ^ 2 * w by ring,
        ← mul_assoc, ← le_div_iff₀ hW.w_pos]
      exact hW.abs_VPhiR_mul_sq_le r

end Bounds

/-! ## Real / even / continuous; values at 0; `v̂² = Â_v`, `V² = ĝ_v`; inversion; Plancherel -/

section Fourier
variable (hW : AdmWindow v L w c)
include hW

omit hW in
lemma vHat_ofReal (heven : ∀ u, v (-u) = v u) (r : ℝ) : vHat v r = (vHatR v r : ℂ) :=
  Taper.paperFT_ofReal_eq_re (v := v) heven r

lemma vHat_ofReal' (r : ℝ) : vHat v r = (vHatR v r : ℂ) := vHat_ofReal hW.even r

lemma VPhi_ofReal (r : ℝ) : VPhi v r = (VPhiR v r : ℂ) :=
  Taper.paperFT_ofReal_eq_re (v := fun u => v u ^ 2) hW.sq_even r

lemma vHatR_even (r : ℝ) : vHatR v (-r) = vHatR v r := by
  simp only [vHatR, vHat, Complex.ofReal_neg, Taper.paperFT_neg_of_even hW.even]

lemma VPhiR_even (r : ℝ) : VPhiR v (-r) = VPhiR v r := by
  simp only [VPhiR, VPhi, Complex.ofReal_neg]
  rw [Taper.paperFT_neg_of_even (v := fun u => v u ^ 2) hW.sq_even]

lemma vHatR_continuous : Continuous (vHatR v) :=
  (Taper.contDiff_re_paperFT_ofReal hW.vC_continuous hW.vC_hasCompactSupport 0).continuous

lemma VPhiR_continuous : Continuous (VPhiR v) :=
  (Taper.contDiff_re_paperFT_ofReal hW.vSqC_continuous hW.vSqC_hasCompactSupport 0).continuous

lemma VPhiR_contDiff_one : ContDiff ℝ 1 (VPhiR v) :=
  Taper.contDiff_re_paperFT_ofReal hW.vSqC_continuous hW.vSqC_hasCompactSupport 1

lemma VPhiR_zero : VPhiR v 0 = av v L * L := by
  have hL : L ≠ 0 := hW.L_pos.ne'
  rw [VPhiR, VPhi, Complex.ofReal_zero, Taper.paperFT_ofReal_zero, Complex.ofReal_re, av,
    mul_comm, ← mul_assoc, mul_inv_cancel₀ hL, one_mul]

lemma gv_zero : gv v 0 = bv v L * L := by
  have hL : L ≠ 0 := hW.L_pos.ne'
  rw [gv, Params.autocorr, bv, mul_comm, ← mul_assoc, mul_inv_cancel₀ hL, one_mul]
  congr 1; funext u; rw [add_zero]; ring

lemma Av_zero : Av v 0 = av v L * L := by
  have hL : L ≠ 0 := hW.L_pos.ne'
  rw [Av, Params.autocorr, av, mul_comm, ← mul_assoc, mul_inv_cancel₀ hL, one_mul]
  congr 1; funext u; rw [add_zero, sq]

/-- `v̂² = (A_v)^` on ℝ. -/
lemma vHatR_sq_eq (r : ℝ) : ((vHatR v r) ^ 2 : ℂ) = paperFT (fun u => (Av v u : ℂ)) r := by
  have h := Taper.paperFT_autocorr (v := v) hW.even hW.continuous hW.hasCompactSupport r
  have h2 : paperFT (fun u => (v u : ℂ)) r = (vHatR v r : ℂ) := hW.vHat_ofReal' r
  rw [h2] at h
  exact h.symm

/-- `V² = (g_v)^` on ℝ. -/
lemma VPhiR_sq_eq (r : ℝ) : ((VPhiR v r) ^ 2 : ℂ) = paperFT (fun u => (gv v u : ℂ)) r := by
  have h := Taper.paperFT_autocorr (v := fun u => v u ^ 2) hW.sq_even hW.sq_continuous
    hW.sq_hasCompactSupport r
  have h2 : paperFT (fun u => (((v u) ^ 2 : ℝ) : ℂ)) r = (VPhiR v r : ℂ) := hW.VPhi_ofReal r
  beta_reduce at h
  rw [h2] at h
  exact h.symm

lemma integrable_vHatR_sq : Integrable (fun r => vHatR v r ^ 2) :=
  (Taper.integrable_re_paperFT_sq_and hW.vC_contDiff hW.vC_supp).1

lemma integrable_vHatR_sq_mul_abs : Integrable (fun r => vHatR v r ^ 2 * |r|) :=
  (Taper.integrable_re_paperFT_sq_and hW.vC_contDiff hW.vC_supp).2

lemma integrable_VPhiR_sq : Integrable (fun x => VPhiR v x ^ 2) :=
  (Taper.integrable_re_paperFT_sq_and hW.vSqC_contDiff hW.vSqC_supp).1

lemma integrable_VPhiR_sq_mul_abs : Integrable (fun x => VPhiR v x ^ 2 * |x|) :=
  (Taper.integrable_re_paperFT_sq_and hW.vSqC_contDiff hW.vSqC_supp).2

/-! #### the autocorrelations -/

set_option linter.unusedSectionVars false in  -- `hW` is unused here but kept so that call sites can write `hW.<name>`
lemma Av_even (y : ℝ) : Av v (-y) = Av v y := Taper.autocorr_even' _ y
set_option linter.unusedSectionVars false in  -- `hW` is unused here but kept so that call sites can write `hW.<name>`
lemma gv_even (y : ℝ) : gv v (-y) = gv v y := Taper.autocorr_even' _ y

lemma integrable_mul_shift (y : ℝ) : Integrable fun u => v u * v (u + y) := by
  have hc := hW.continuous
  refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
  exact HasCompactSupport.intro (K := Icc (-(L / 2)) (L / 2)) isCompact_Icc fun u hu => by
    rw [hW.eq_zero_of_not_mem hu, zero_mul]

lemma integrable_sq_mul_shift (y : ℝ) : Integrable fun u => v u ^ 2 * v (u + y) ^ 2 := by
  have hc := hW.continuous
  refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
  exact HasCompactSupport.intro (K := Icc (-(L / 2)) (L / 2)) isCompact_Icc fun u hu => by
    rw [hW.eq_zero_of_not_mem hu]; ring

set_option linter.unusedSectionVars false in  -- `hW` is unused here but kept so that call sites can write `hW.<name>`
lemma gv_nonneg (y : ℝ) : 0 ≤ gv v y :=
  integral_nonneg fun u => mul_nonneg (sq_nonneg _) (sq_nonneg _)

lemma gv_le_Av (y : ℝ) : gv v y ≤ Av v y := by
  unfold gv Av Params.autocorr
  refine integral_mono_of_nonneg (ae_of_all _ fun u => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (hW.integrable_mul_shift y) (ae_of_all _ fun u => ?_)
  exact mul_le_mul (hW.sq_le_self _) (hW.sq_le_self _) (sq_nonneg _) (hW.nonneg _)

lemma Av_le (y : ℝ) : Av v y ≤ max (L - |y|) 0 := by
  have h := Taper.autocorr_le_of_support v (M := L / 2) hW.nonneg hW.le_one hW.support y
  rw [show 2 * (L / 2) = L by ring] at h
  exact h

lemma Av_nonneg (y : ℝ) : 0 ≤ Av v y := le_trans (hW.gv_nonneg y) (hW.gv_le_Av y)

lemma gv_eq_zero {y : ℝ} (hy : L ≤ |y|) : gv v y = 0 :=
  Taper.autocorr_eq_zero_of_support (fun u => v u ^ 2) (M := L / 2) hW.sq_eq_zero (by linarith)

lemma Av_eq_zero {y : ℝ} (hy : L ≤ |y|) : Av v y = 0 :=
  Taper.autocorr_eq_zero_of_support v (M := L / 2) hW.support (by linarith)

lemma gv_continuous : Continuous (gv v) :=
  Taper.autocorr_continuous_of_support (fun u => v u ^ 2) (M := L / 2) hW.sq_continuous hW.sq_eq_zero

lemma Av_continuous : Continuous (Av v) :=
  Taper.autocorr_continuous_of_support v (M := L / 2) hW.continuous hW.support

/-! #### inversion (cosine form) and Plancherel -/

lemma integral_vHatR_sq_mul_cos (y : ℝ) :
    ∫ r, vHatR v r ^ 2 * Real.cos (r * y) = 2 * π * Av v y :=
  Taper.integral_mul_cos_of_paperFT_eq (A := Av v) (G := fun r => vHatR v r ^ 2)
    (Taper.autocorr_continuous_of_even hW.even hW.continuous hW.hasCompactSupport)
    (Taper.autocorr_integrable_of_even hW.even hW.continuous hW.hasCompactSupport)
    hW.integrable_vHatR_sq
    (fun r => by rw [← hW.vHatR_sq_eq r]; push_cast; ring) y

lemma integral_VPhiR_sq_mul_cos (y : ℝ) :
    ∫ x, VPhiR v x ^ 2 * Real.cos (x * y) = 2 * π * gv v y :=
  Taper.integral_mul_cos_of_paperFT_eq (A := gv v) (G := fun r => VPhiR v r ^ 2)
    (Taper.autocorr_continuous_of_even hW.sq_even hW.sq_continuous hW.sq_hasCompactSupport)
    (Taper.autocorr_integrable_of_even hW.sq_even hW.sq_continuous hW.sq_hasCompactSupport)
    hW.integrable_VPhiR_sq
    (fun r => by rw [← hW.VPhiR_sq_eq r]; push_cast; ring) y

lemma integral_vHatR_sq : ∫ r, vHatR v r ^ 2 = 2 * π * av v L * L := by
  have h := hW.integral_vHatR_sq_mul_cos 0
  simp only [mul_zero, Real.cos_zero, mul_one] at h
  rw [h, hW.Av_zero]
  ring

lemma integral_VPhiR_sq : ∫ r, VPhiR v r ^ 2 = 2 * π * bv v L * L := by
  have h := hW.integral_VPhiR_sq_mul_cos 0
  simp only [mul_zero, Real.cos_zero, mul_one] at h
  rw [h, hW.gv_zero]
  ring

end Fourier

/-! ## [lem:poisson] for the window -/

section Poisson
variable (hW : AdmWindow v L w c)
include hW

lemma vHat_decay : ∃ C, ∀ s : ℝ, ‖paperFT (fun u => (v u : ℂ)) s‖ * (1 + s ^ 2) ≤ C := by
  refine ⟨L + ∫ u, |deriv (deriv v) u|, fun s => ?_⟩
  have h0 := hW.norm_vHat_le s
  have h2 := hW.norm_vHat_mul_sq_le s
  simp only [ofReal_im, abs_zero, zero_mul, Real.exp_zero, one_mul, norm_real,
    Real.norm_eq_abs, sq_abs] at h0 h2
  unfold vHat at h0 h2
  linarith

/-- `Σ_{k∈ℤ} v̂(τ−τ_k) v̂(τ'−τ_k) = L · V(τ−τ')`, `τ_k = T + k·2π/L`. -/
theorem hasSum_vHatR_mul (T τ τ' : ℝ) :
    HasSum (fun k : ℤ => vHatR v (τ - (T + k * (2 * π / L))) * vHatR v (τ' - (T + k * (2 * π / L))))
      (L * VPhiR v (τ - τ')) := by
  have h := Poisson.hasSum_paperFT_mul_paperFT hW.L_pos hW.continuous hW.support hW.even
    hW.vHat_decay T τ τ'
  have h2 := (Complex.reCLM.hasSum h)
  convert h2 using 1
  · funext k
    simp only [Complex.reCLM_apply]
    rw [show paperFT (fun u => (v u : ℂ)) = vHat v from rfl, hW.vHat_ofReal', hW.vHat_ofReal']
    norm_cast
  · simp only [Complex.reCLM_apply]
    rw [show paperFT (fun u => (((v u) ^ 2 : ℝ) : ℂ)) = VPhi v from rfl, hW.VPhi_ofReal]
    norm_cast

end Poisson

/-! ## [eq:abdef] without the flat top: `0 ≤ b ≤ a ≤ 1` -/

section AB
variable (hW : AdmWindow v L w c)
include hW

lemma bv_le_av : bv v L ≤ av v L := by
  unfold bv av
  have hmono : ∫ u : ℝ, v u ^ 4 ≤ ∫ u : ℝ, v u ^ 2 := by
    refine integral_mono (hW.integrable_pow (by norm_num)) (hW.integrable_pow (by norm_num)) fun u => ?_
    have hp2 : v u ^ 2 ≤ 1 := pow_le_one₀ (hW.nonneg u) (hW.le_one u)
    have hp2n : (0 : ℝ) ≤ v u ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left hp2 hp2n]
  exact mul_le_mul_of_nonneg_left hmono (by have := hW.L_pos; positivity)

lemma av_le_one : av v L ≤ 1 := by
  unfold av
  calc L⁻¹ * ∫ u : ℝ, v u ^ 2 ≤ L⁻¹ * L :=
        mul_le_mul_of_nonneg_left hW.integral_sq_le (by have := hW.L_pos; positivity)
    _ = 1 := inv_mul_cancel₀ hW.L_pos.ne'

lemma bv_nonneg : 0 ≤ bv v L := by
  unfold bv
  have h : (0 : ℝ) ≤ ∫ u : ℝ, v u ^ 4 := integral_nonneg fun u => by
    have := hW.nonneg u; positivity
  have := hW.L_pos
  positivity

end AB

end AdmWindow

end Zeta23

end
