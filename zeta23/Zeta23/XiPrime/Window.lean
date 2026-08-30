/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Window.lean — the window functional c_λ(v; D) and its limits.

[XF′] Thm 8.1/8.2, Remark 7.2.  Objects (Zeta23/XiPrime/Defs.lean §4):
  vConv v r   = (v⋆v)(r) = ∫_{-1/2}^{1/2−r} v(s)v(s+r) ds,
  jWin D λ v  = 𝒥_D(λ;v) = 2∫₀¹ D(λr)(v⋆v)(r) dr,
  cWin D λ v  = c_λ(v;D) = λ(∫v)²/(∫v² + λ·𝒥_D(λ;v)),      kappaXi λ v = 1/c_λ(v;D₁).
This file is the ξ′ analogue of Zeta23/ThmD/{Limit,Window}.lean (there D(s) = s, v = v*):
 (W1) algebra/positivity: ThmD.cRatio λ (∫v) (∫v²) (𝒥/λ) = c_λ(v;D); c > 0;
 (W2) the abstract T → ∞ limit the prime side consumes (CoeffMoments):
      λ₁(T) → λ, a_T → ∫v, b_T → ∫v², J_T → 𝒥_D(λ;v)/λ  ⟹  cRatio(λ₁(T); a_T, b_T, J_T) → c_λ(v;D),
      and J_T → 𝒥/λ from a POINTWISE autocorrelation comparison |g_T(y) − L·(v⋆v)(y/L)| ≤ C·w on [0,L]
      (J_T := (2/L³)·l·∫₀ᴸ D(y/l)·g_T(y) dy, the prime-side definition verbatim; since L = λ·l EXACTLY,
      D(y/l) = D(λ·y/L) and no continuity of D in λ is needed for this step);
 (W3) the FLAT window end to end: a_T, b_T → 1 and J_T → 𝒥_D(λ;1)/λ for the tree's own taper P.phi;
 (W4) continuity of λ ↦ c_λ(v;D), κ₁(λ,v) on (0,1] ([XF′ Remark 7.2]: "c_λ(v) is continuous in λ ∈ (0,1]
      (a ratio of integrals of the continuous D₁ against v⊗v)") and the λ → 1⁻ devices: from a STRICT
      inequality at λ = 1 to some λ ∈ [1/2,1) (for the ε-free CertFlat/CertQuartic), and the ε-step
      (for the limit form);
 (W5) WindowProfile vFlat / vQuartic (Statement.lean §4).
-/
import Zeta23.XiPrime.Statement
import Zeta23.XiPrime.Certificate.Poly
import Zeta23.ThmD.Limit

open Set Filter Topology intervalIntegral MeasureTheory

noncomputable section

namespace Zeta23
namespace XiPrime

/-! ## (W1) algebra and positivity -/

section Algebra
variable {D v : ℝ → ℝ} {lam : ℝ}

/-- the tree's ratio constant at J := 𝒥_D(λ;v)/λ IS c_λ(v;D). -/
theorem cRatio_eq_cWin (D v : ℝ → ℝ) (hlam : lam ≠ 0) :
    ThmD.cRatio lam (∫ s in (-(1:ℝ)/2)..(1/2), v s) (∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2)
      (jWin D lam v / lam) = cWin D lam v := by
  unfold ThmD.cRatio cWin
  have : lam ^ 2 * (jWin D lam v / lam) = lam * jWin D lam v := by
    field_simp
  rw [this]

/-- (v⋆v) ≥ 0 on [0,1] when v ≥ 0 on the window. -/
theorem vConv_nonneg (hv : ∀ s ∈ Icc (-(1:ℝ)/2) (1/2), 0 ≤ v s) {r : ℝ} (hr : r ∈ Icc (0:ℝ) 1) :
    0 ≤ vConv v r := by
  unfold vConv
  apply intervalIntegral.integral_nonneg (by linarith [hr.2])
  intro s hs
  exact mul_nonneg (hv s ⟨hs.1, by linarith [hs.2, hr.1]⟩)
    (hv (s + r) ⟨by linarith [hs.1, hr.1], by linarith [hs.2]⟩)

/-- 𝒥_D(λ;v) ≥ 0 for 0 ≤ λ ≤ 1, D ≥ 0 on [0,1], v ≥ 0 on the window. -/
theorem jWin_nonneg (hD : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ D x) (hv : ∀ s ∈ Icc (-(1:ℝ)/2) (1/2), 0 ≤ v s)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) : 0 ≤ jWin D lam v := by
  unfold jWin
  refine mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg zero_le_one fun r hr => ?_)
  refine mul_nonneg (hD _ ⟨mul_nonneg h0 hr.1, ?_⟩) (vConv_nonneg hv hr)
  calc lam * r ≤ 1 * 1 := mul_le_mul h1 hr.2 hr.1 zero_le_one
    _ = 1 := one_mul 1

/-- c_λ(v;D) > 0 for 0 < λ ≤ 1 when ∫v ≠ 0, ∫v² > 0, 𝒥 ≥ 0. -/
theorem cWin_pos (ha : (∫ s in (-(1:ℝ)/2)..(1/2), v s) ≠ 0)
    (hb : 0 < ∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2) (hJ : 0 ≤ jWin D lam v) (h0 : 0 < lam) :
    0 < cWin D lam v := by
  unfold cWin
  apply div_pos (mul_pos h0 (by positivity))
  have := mul_nonneg h0.le hJ
  linarith

theorem cWin_denom_pos (hb : 0 < ∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2) (hJ : 0 ≤ jWin D lam v)
    (h0 : 0 ≤ lam) : 0 < (∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2) + lam * jWin D lam v := by
  have := mul_nonneg h0 hJ; linarith

end Algebra

/-! ## (W2) the abstract T → ∞ limit -/

section Limit
variable {D v : ℝ → ℝ}

/-- generic ratio limit (mirror of ThmD.Limit.tendsto_cRatio_of): any λ₁-like sequence → λ and any data
→ (∫v, ∫v², 𝒥_D(λ;v)/λ) give cRatio → c_λ(v;D). -/
theorem tendsto_cRatio_cWin {lam : ℝ} (h0 : 0 < lam) {lam1f aT bT JT : ℝ → ℝ}
    (hl1 : Tendsto lam1f atTop (𝓝 lam))
    (ha : Tendsto aT atTop (𝓝 (∫ s in (-(1:ℝ)/2)..(1/2), v s)))
    (hb : Tendsto bT atTop (𝓝 (∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2)))
    (hJ : Tendsto JT atTop (𝓝 (jWin D lam v / lam)))
    (hden : 0 < (∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2) + lam * jWin D lam v) :
    Tendsto (fun T => ThmD.cRatio (lam1f T) (aT T) (bT T) (JT T)) atTop (𝓝 (cWin D lam v)) := by
  set a := ∫ s in (-(1:ℝ)/2)..(1/2), v s
  set b := ∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2
  have hnum : Tendsto (fun T => lam1f T * (aT T) ^ 2) atTop (𝓝 (lam * a ^ 2)) := hl1.mul (ha.pow 2)
  have hdenT : Tendsto (fun T => bT T + (lam1f T) ^ 2 * JT T) atTop
      (𝓝 (b + lam ^ 2 * (jWin D lam v / lam))) := hb.add ((hl1.pow 2).mul hJ)
  have hden' : b + lam ^ 2 * (jWin D lam v / lam) = b + lam * jWin D lam v := by
    congr 1; field_simp
  rw [hden'] at hdenT
  have hlim := hnum.div hdenT (ne_of_gt hden)
  unfold cWin
  exact hlim

/-- (v⋆v) is continuous when v is (parametric interval integral with moving endpoint). -/
theorem continuous_vConv (hv : Continuous v) : Continuous (vConv v) := by
  unfold vConv
  have h : Continuous (Function.uncurry fun (r s : ℝ) => v s * v (s + r)) := by
    exact (hv.comp continuous_snd).mul (hv.comp (continuous_snd.add continuous_fst))
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous h
    (continuous_const.sub continuous_id)

/-- **J_T → 𝒥_D(λ;v)/λ** from a pointwise autocorrelation comparison, where
J_T := (2/L³)·l·∫₀ᴸ D(y/l)·g_T(y) dy.  Hypotheses: D continuous on [0,1]; v continuous; eventually g_T is
continuous and |g_T(y) − L·(v⋆v)(y/L)| ≤ C·w for y ∈ [0, L]. -/
theorem tendsto_JT_of_autocorr_close {P : Params} (hP : P.Valid) (hD : ContinuousOn D (Icc 0 1))
    (hv : Continuous v) {g : ℝ → ℝ → ℝ} {C : ℝ}
    (hgc : ∀ᶠ T in atTop, Continuous (g T))
    (hg : ∀ᶠ T in atTop, ∀ y ∈ Icc (0:ℝ) (P.L T), |g T y - P.L T * vConv v (y / P.L T)| ≤ C * P.w) :
    Tendsto (fun T => 2 / P.L T ^ 3 * l T * ∫ y in (0:ℝ)..P.L T, (D (y / l T) * g T y))
      atTop (𝓝 (jWin D P.lam v / P.lam)) := by
  have hlam := hP.lam_pos
  have hlam1 := hP.lam_le_one
  -- a bound for |D| on [0,1]
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hD
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 ⟨le_rfl, zero_le_one⟩)
  -- eventually: l > 0, L > 0, and the two g-hypotheses
  have hev : ∀ᶠ T in atTop, |2 / P.L T ^ 3 * l T * (∫ y in (0:ℝ)..P.L T, (D (y / l T) * g T y))
      - jWin D P.lam v / P.lam| ≤ (2 * M * |C| / P.lam) * P.w / P.L T := by
    filter_upwards [Assembly.eventually_l_pos, hgc, hg] with T hl hgcT hgT
    have hL : 0 < P.L T := by unfold Params.L; exact mul_pos hlam hl
    have hLl : P.L T = P.lam * l T := rfl
    -- D(λ r) is continuous on [0,1]
    have hDl : ContinuousOn (fun r : ℝ => D (P.lam * r)) (Icc 0 1) := by
      refine hD.comp (continuous_const.mul continuous_id).continuousOn ?_
      intro r hr
      exact ⟨mul_nonneg hlam.le hr.1, by nlinarith [hr.2, hlam1, hr.1]⟩
    -- change of variables y = L r
    have hsub : ∫ y in (0:ℝ)..P.L T, (D (y / l T) * g T y)
        = P.L T * ∫ r in (0:ℝ)..1, (D (P.lam * r) * g T (P.L T * r)) := by
      have hc := intervalIntegral.integral_comp_mul_left (fun y => D (y / l T) * g T y) (ne_of_gt hL)
        (a := 0) (b := 1)
      simp only [mul_zero, mul_one, smul_eq_mul] at hc
      have hker : (fun r => D (P.L T * r / l T) * g T (P.L T * r))
          = fun r => D (P.lam * r) * g T (P.L T * r) := by
        ext r
        have : P.L T * r / l T = P.lam * r := by rw [hLl]; field_simp
        rw [this]
      rw [hker] at hc
      rw [hc]; field_simp
    -- the target in the same currency
    have htar : jWin D P.lam v / P.lam
        = 2 / (P.lam * P.L T) * ∫ r in (0:ℝ)..1, (D (P.lam * r) * (P.L T * vConv v r)) := by
      unfold jWin
      have : (fun r => D (P.lam * r) * (P.L T * vConv v r))
          = fun r => P.L T * (D (P.lam * r) * vConv v r) := by
        ext r; ring
      rw [this, intervalIntegral.integral_const_mul]
      field_simp
    have hJT : 2 / P.L T ^ 3 * l T * ∫ y in (0:ℝ)..P.L T, (D (y / l T) * g T y)
        = 2 / (P.lam * P.L T) * ∫ r in (0:ℝ)..1, (D (P.lam * r) * g T (P.L T * r)) := by
      rw [hsub]
      have hl' : l T = P.L T / P.lam := by rw [hLl]; field_simp
      rw [hl']
      field_simp
    rw [hJT, htar, ← mul_sub]
    -- integrability
    have hi1 : IntervalIntegrable (fun r => D (P.lam * r) * g T (P.L T * r)) volume 0 1 :=
      (hDl.mul (hgcT.comp (continuous_const.mul continuous_id)).continuousOn).intervalIntegrable_of_Icc
        zero_le_one
    have hi2 : IntervalIntegrable (fun r => D (P.lam * r) * (P.L T * vConv v r)) volume 0 1 :=
      (hDl.mul (continuous_const.mul (continuous_vConv hv)).continuousOn).intervalIntegrable_of_Icc
        zero_le_one
    rw [← intervalIntegral.integral_sub hi1 hi2]
    -- pointwise bound of the difference integrand by M·|C|·w
    have hpt : ∀ r ∈ Set.uIoc (0:ℝ) 1,
        ‖D (P.lam * r) * g T (P.L T * r) - D (P.lam * r) * (P.L T * vConv v r)‖ ≤ M * (|C| * P.w) := by
      intro r hr
      rw [uIoc_of_le zero_le_one] at hr
      have hr' : r ∈ Icc (0:ℝ) 1 := ⟨hr.1.le, hr.2⟩
      rw [← mul_sub, norm_mul]
      have hy : P.L T * r ∈ Icc 0 (P.L T) := ⟨mul_nonneg hL.le hr'.1, by nlinarith [hr'.2, hL]⟩
      have hg1 := hgT (P.L T * r) hy
      have hdiv : P.L T * r / P.L T = r := by field_simp
      rw [hdiv] at hg1
      have hD1 : ‖D (P.lam * r)‖ ≤ M :=
        hM _ ⟨mul_nonneg hlam.le hr'.1, by nlinarith [hr'.2, hlam1, hr'.1]⟩
      have hg2 : ‖g T (P.L T * r) - P.L T * vConv v r‖ ≤ |C| * P.w := by
        rw [Real.norm_eq_abs]
        exact hg1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (le_of_lt (Params.w_pos hP)))
      exact mul_le_mul hD1 hg2 (norm_nonneg _) hM0
    have hint := intervalIntegral.norm_integral_le_of_norm_le_const hpt
    rw [Real.norm_eq_abs, sub_zero, abs_one, mul_one] at hint
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 / (P.lam * P.L T))]
    calc 2 / (P.lam * P.L T) * |∫ r in (0:ℝ)..1,
          (D (P.lam * r) * g T (P.L T * r) - D (P.lam * r) * (P.L T * vConv v r))|
        ≤ 2 / (P.lam * P.L T) * (M * (|C| * P.w)) := mul_le_mul_of_nonneg_left hint (by positivity)
      _ = 2 * M * |C| / P.lam * P.w / P.L T := by field_simp
  exact ThmD.tendsto_of_close hlam hev

end Limit

/-! ## (W3) the flat window, concretely (the tree's taper P.phi; v = vFlat) -/

section Flat
variable {P : Params}

theorem jWin_vFlat (D : ℝ → ℝ) (lam : ℝ) :
    jWin D lam vFlat = 2 * ∫ r in (0:ℝ)..1, (D (lam * r) * (1 - r)) := by
  unfold jWin; simp_rw [vConv_vFlat]

theorem cWin_vFlat (D : ℝ → ℝ) (lam : ℝ) : cWin D lam vFlat = lam / (1 + lam * jWin D lam vFlat) := by
  unfold cWin; rw [integral_vFlat, integral_vFlat_sq]; ring

/-- κ₁(λ, flat) = 1/λ + 2∫₀¹ D₁(λr)(1−r) dr  (the ζ analogue is Zeta23.kfun λ = 1/λ + λ/3). -/
theorem kappaXi_vFlat {lam : ℝ} (h0 : lam ≠ 0) :
    kappaXi lam vFlat = 1 / lam + jWin D1 lam vFlat := by
  unfold kappaXi; rw [cWin_vFlat]; field_simp

theorem eventually_w8 (hP : P.Valid) : ∀ᶠ T in atTop, 8 * P.w ≤ P.L T :=
  (Assembly.tendsto_L_atTop P hP.lam_pos).eventually_ge_atTop _

/-- a_T → 1 = ∫ vFlat for the flat taper. -/
theorem tendsto_a_flat (hP : P.Valid) :
    Tendsto (fun T => P.a T) atTop (𝓝 (∫ s in (-(1:ℝ)/2)..(1/2), vFlat s)) := by
  rw [integral_vFlat]
  apply ThmD.tendsto_of_close hP.lam_pos (C := 2)
  filter_upwards [eventually_w8 hP] with T hT
  have h1 := Params.a_le_one hP hT
  have h2 := Params.one_sub_le_b hP hT
  have h3 := Params.b_le_a hP hT
  rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  linarith

/-- b_T → 1 = ∫ vFlat² for the flat taper. -/
theorem tendsto_b_flat (hP : P.Valid) :
    Tendsto (fun T => P.b T) atTop (𝓝 (∫ s in (-(1:ℝ)/2)..(1/2), vFlat s ^ 2)) := by
  rw [integral_vFlat_sq]
  apply ThmD.tendsto_of_close hP.lam_pos (C := 2)
  filter_upwards [eventually_w8 hP] with T hT
  have h1 := Params.a_le_one hP hT
  have h2 := Params.one_sub_le_b hP hT
  have h3 := Params.b_le_a hP hT
  rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  linarith

/-- the flat autocorrelation is within 2w of the sharp one: |g(y) − (L − y)| ≤ 2w on [0, L]. -/
theorem g_flat_close (hP : P.Valid) {T : ℝ} (hT : 8 * P.w ≤ P.L T) {y : ℝ} (hy : y ∈ Icc (0:ℝ) (P.L T)) :
    |P.g T y - P.L T * vConv vFlat (y / P.L T)| ≤ 2 * P.w := by
  have hL : 0 < P.L T := by linarith [hP.one_le_w]
  rw [vConv_vFlat]
  have hmain : P.L T * (1 - y / P.L T) = P.L T - y := by field_simp
  rw [hmain]
  have hyabs : |y| = y := abs_of_nonneg hy.1
  have hlo := Params.g_ge hP hT y
  have hhi := (Params.g_le_Aphi hP hT y).trans (Params.Aphi_le hP hT y)
  rw [hyabs] at hlo hhi
  have hmax1 : max (P.L T - y) 0 = P.L T - y := max_eq_left (by linarith [hy.2])
  rw [hmax1] at hhi
  have hlo' : P.L T - 2 * P.w - y ≤ P.g T y := le_trans (le_max_left _ _) hlo
  rw [abs_le]; constructor <;> linarith

/-- **J_T → 𝒥_D(λ; flat)/λ** for the flat taper. -/
theorem tendsto_JT_flat (hP : P.Valid) {D : ℝ → ℝ} (hD : ContinuousOn D (Icc 0 1)) :
    Tendsto (fun T => 2 / P.L T ^ 3 * l T * ∫ y in (0:ℝ)..P.L T, (D (y / l T) * P.g T y))
      atTop (𝓝 (jWin D P.lam vFlat / P.lam)) := by
  refine tendsto_JT_of_autocorr_close (g := fun T => P.g T) (C := 2) hP hD continuous_const ?_ ?_
  · filter_upwards [eventually_w8 hP] with T hT using Params.g_continuous hP hT
  · filter_upwards [eventually_w8 hP] with T hT
    intro y hy
    exact g_flat_close hP hT hy

/-- **the flat-window ratio limit**, packaged for CoeffMoments:
cRatio(λ₁(T); a_T, b_T, J_T) → c_λ(1; D) for the tree's taper, any continuous D ≥ 0 on [0,1]. -/
theorem tendsto_cRatio_flat (hP : P.Valid) {D : ℝ → ℝ} (hD : ContinuousOn D (Icc 0 1))
    (hD0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ D x) :
    Tendsto (fun T => ThmD.cRatio (P.lam1 T) (P.a T) (P.b T)
      (2 / P.L T ^ 3 * l T * ∫ y in (0:ℝ)..P.L T, (D (y / l T) * P.g T y))) atTop
      (𝓝 (cWin D P.lam vFlat)) := by
  refine tendsto_cRatio_cWin hP.lam_pos (ThmD.tendsto_lam1 hP.lam_pos) (tendsto_a_flat hP)
    (tendsto_b_flat hP) (tendsto_JT_flat hP hD) ?_
  rw [integral_vFlat_sq]
  have := jWin_nonneg (v := vFlat) hD0 (fun s _ => by simp [vFlat]) hP.lam_pos.le hP.lam_le_one
  have := mul_nonneg hP.lam_pos.le this
  linarith

theorem cWin_vFlat_pos {D : ℝ → ℝ} (hD0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ D x) {lam : ℝ} (h0 : 0 < lam)
    (h1 : lam ≤ 1) : 0 < cWin D lam vFlat := by
  apply cWin_pos
  · rw [integral_vFlat]; norm_num
  · rw [integral_vFlat_sq]; norm_num
  · exact jWin_nonneg hD0 (fun s _ => by simp [vFlat]) h0.le h1
  · exact h0

end Flat

/-! ## (W4) continuity in λ and the λ → 1⁻ devices -/

section Continuity
variable {D v : ℝ → ℝ}

/-- λ ↦ 𝒥_D(λ;v) is continuous (D, v continuous). -/
theorem continuous_jWin (hD : Continuous D) (hv : Continuous v) :
    Continuous fun lam => jWin D lam v := by
  unfold jWin
  refine continuous_const.mul ?_
  have h : Continuous (Function.uncurry fun (lam r : ℝ) => D (lam * r) * vConv v r) :=
    (hD.comp (continuous_fst.mul continuous_snd)).mul ((continuous_vConv hv).comp continuous_snd)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' h 0 1

/-- λ ↦ c_λ(v;D) is continuous on [0,1] (D ≥ 0 on [0,1], v continuous and ≥ 0 on the window, ∫v² > 0). -/
theorem continuousOn_cWin (hD : Continuous D) (hD0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ D x) (hv : Continuous v)
    (hv0 : ∀ s ∈ Icc (-(1:ℝ)/2) (1/2), 0 ≤ v s) (hb : 0 < ∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2) :
    ContinuousOn (fun lam => cWin D lam v) (Icc 0 1) := by
  unfold cWin
  refine ContinuousOn.div (by fun_prop) ?_ ?_
  · exact (continuousOn_const.add (continuousOn_id.mul (continuous_jWin hD hv).continuousOn))
  · intro lam hlam
    exact ne_of_gt (cWin_denom_pos hb (jWin_nonneg hD0 hv0 hlam.1 hlam.2) hlam.1)

/-- λ ↦ κ(λ) := 1/c_λ(v;D) is continuous on (0,1]. -/
theorem continuousOn_inv_cWin (hD : Continuous D) (hD0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ D x)
    (hv : Continuous v) (hv0 : ∀ s ∈ Icc (-(1:ℝ)/2) (1/2), 0 ≤ v s)
    (ha : (∫ s in (-(1:ℝ)/2)..(1/2), v s) ≠ 0) (hb : 0 < ∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2) :
    ContinuousOn (fun lam => 1 / cWin D lam v) (Ioc 0 1) := by
  refine ContinuousOn.div continuousOn_const
    ((continuousOn_cWin hD hD0 hv hv0 hb).mono Ioc_subset_Icc_self) ?_
  intro lam hlam
  exact ne_of_gt (cWin_pos ha hb (jWin_nonneg hD0 hv0 hlam.1.le hlam.2) hlam.1)

/-- **κ₁(·, v) is continuous on (0,1]** for any continuous v ≥ 0 on the window with ∫v ≠ 0. -/
theorem continuousOn_kappaXi (hv : Continuous v) (hv0 : ∀ s ∈ Icc (-(1:ℝ)/2) (1/2), 0 ≤ v s)
    (ha : (∫ s in (-(1:ℝ)/2)..(1/2), v s) ≠ 0) (hb : 0 < ∫ s in (-(1:ℝ)/2)..(1/2), v s ^ 2) :
    ContinuousOn (fun lam => kappaXi lam v) (Ioc 0 1) :=
  continuousOn_inv_cWin continuous_D1 (fun _ hx => D1_nonneg hx.1) hv hv0 ha hb

/-- from a strict inequality at λ = 1 to one at some λ ∈ [1/2, 1): if f is continuous on [1/2,1]
and 0 < f 1 then 0 < f λ for some λ ∈ [1/2,1). -/
theorem exists_lt_one_pos {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (1/2) 1)) (h1 : 0 < f 1) :
    ∃ lam : ℝ, 1 / 2 ≤ lam ∧ lam < 1 ∧ 0 < f lam := by
  have hc : ContinuousWithinAt f (Icc (1/2) 1) 1 := hf 1 ⟨by norm_num, le_rfl⟩
  rw [Metric.continuousWithinAt_iff] at hc
  obtain ⟨δ, hδ, hδf⟩ := hc (f 1) h1
  refine ⟨max (1/2) (1 - δ/2), le_max_left _ _, max_lt (by norm_num) (by linarith), ?_⟩
  set lam := max (1/2 : ℝ) (1 - δ/2)
  have hmem : lam ∈ Icc (1/2 : ℝ) 1 := ⟨le_max_left _ _, max_le (by norm_num) (by linarith)⟩
  have hdist : dist lam 1 < δ := by
    rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [hmem.2])]
    have : 1 - δ/2 ≤ lam := le_max_right _ _
    linarith
  have h := hδf hmem hdist
  rw [Real.dist_eq] at h
  linarith [abs_lt.mp h]

/-- the λ → 1⁻ ε-step (ξ′ analogue of ThmD.Limit.eps_form_cStar, continuity in place of Lipschitz):
if a rate g is continuous on [1/2,1] and the ε-statement holds with constant g λ at every λ ∈ [1/2,1),
it holds with constant g 1. -/
theorem eps_form_of_continuousOn {g N lower : ℝ → ℝ} (hg : ContinuousOn g (Icc (1/2) 1))
    (hN : ∀ T, 0 ≤ N T)
    (h : ∀ lam : ℝ, 1/2 ≤ lam → lam < 1 → ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (g lam - ε) * N T ≤ lower T) :
    ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (g 1 - ε) * N T ≤ lower T := by
  apply ThmD.eps_form_of_approx _ hN h
  intro δ hδ
  obtain ⟨lam, h1, h2, h3⟩ := exists_lt_one_pos (f := fun lam => g lam - (g 1 - δ))
    (hg.sub continuousOn_const) (by simp [hδ])
  exact ⟨lam, h1, h2, by linarith⟩

end Continuity

/-! ## (W5) the two profiles are admissible WindowProfiles -/

theorem windowProfile_vFlat : WindowProfile vFlat where
  even := fun _ => rfl
  contDiff := contDiff_const
  pos := fun _ _ => by simp [vFlat]
  le_one := fun _ => by simp [vFlat]

theorem windowProfile_vQuartic : WindowProfile vQuartic where
  even := vQuartic_even
  contDiff := by unfold vQuartic; fun_prop
  pos := fun _ hs => vQuartic_pos hs
  le_one := vQuartic_le_one

/-- κ₁(·, vFlat) and κ₁(·, vQuartic) are continuous on (0,1]. -/
theorem continuousOn_kappaXi_vFlat : ContinuousOn (fun lam => kappaXi lam vFlat) (Ioc 0 1) :=
  continuousOn_kappaXi continuous_const (fun _ _ => by simp [vFlat])
    (by rw [integral_vFlat]; norm_num) (by rw [integral_vFlat_sq]; norm_num)

theorem continuousOn_kappaXi_vQuartic : ContinuousOn (fun lam => kappaXi lam vQuartic) (Ioc 0 1) :=
  continuousOn_kappaXi continuous_vQuartic (fun _ hs => vQuartic_nonneg_on hs)
    (by rw [integral_vQuartic]; norm_num) (by rw [integral_vQuartic_sq]; norm_num)

theorem cWin_D1_vFlat_pos {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) : 0 < cWin D1 lam vFlat :=
  cWin_vFlat_pos (fun _ hx => D1_nonneg hx.1) h0 h1

theorem cWin_D1_vQuartic_pos {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) : 0 < cWin D1 lam vQuartic :=
  cWin_pos (by rw [integral_vQuartic]; norm_num) (by rw [integral_vQuartic_sq]; norm_num)
    (jWin_nonneg (fun _ hx => D1_nonneg hx.1) (fun _ hs => vQuartic_nonneg_on hs) h0.le h1) h0

theorem kappaXi_pos_vFlat {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) : 0 < kappaXi lam vFlat := by
  unfold kappaXi; exact one_div_pos.mpr (cWin_D1_vFlat_pos h0 h1)

theorem kappaXi_pos_vQuartic {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) : 0 < kappaXi lam vQuartic := by
  unfold kappaXi; exact one_div_pos.mpr (cWin_D1_vQuartic_pos h0 h1)

end XiPrime
end Zeta23
