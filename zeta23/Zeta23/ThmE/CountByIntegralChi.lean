/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmE/CountByIntegralChi.lean — the zero count of L(s,χ) as a contour integral
(χ-analogue of Zeta23/RvM/CountByIntegral.lean).

Λ_sym(s,χ) := q^{s/2}·Λ(s,χ) (Λ = Mathlib's completedLFunction χ, which omits the conductor power):
for primitive χ mod q > 1, Λ_sym is entire, satisfies
Λ_sym(1−s,χ) = W(χ)·Λ_sym(s,χ⁻¹) (W = rootNumber χ ≠ 0), its zeros are exactly the nontrivial zeros
of L(s,χ) (Λ = γ·L on Re s > 0 with γ ≠ 0 [SeamL], L ≠ 0 on Re s ≥ 1 [Mathlib], and the FE for
Re s ≤ 0), with the same analytic orders on the strip. Hence, for heights T₁ ≤ T₂ (ANY sign — no pole)
avoiding the ordinates of zeros,
    (1/2πi) ∮_{∂([−1,2]×[T₁,T₂])} Λ_sym'/Λ_sym = N_χ(T₁,T₂)        (Zeta23.Analytic.rectangleIntegral'_mul_logDeriv).
-/
import Zeta23.Analytic.RectangleLogDeriv
import Zeta23.ThmE.SeamL

open Complex Set Topology Filter Real DirichletCharacter

noncomputable section

namespace Zeta23
namespace ThmE

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-! ## Λ_sym -/

/-- Λ_sym(s,χ) := q^{s/2} · Λ(s,χ) — the symmetrically normalised completed L-function. -/
def completedLSym (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  (q : ℂ) ^ (s / 2) * completedLFunction χ s

lemma natCast_q_ne_zero : (q : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne q

lemma qpow_ne_zero (s : ℂ) : (q : ℂ) ^ (s / 2) ≠ 0 := by
  intro h
  exact natCast_q_ne_zero (q := q) ((cpow_eq_zero_iff _ _).mp h).1

lemma differentiable_qpow : Differentiable ℂ (fun s : ℂ => (q : ℂ) ^ (s / 2)) := fun _ =>
  ((differentiableAt_id.div_const 2).const_cpow (Or.inl natCast_q_ne_zero))

lemma hasDerivAt_qpow (s : ℂ) :
    HasDerivAt (fun s : ℂ => (q : ℂ) ^ (s / 2)) ((q : ℂ) ^ (s / 2) * Complex.log q * (1 / 2)) s := by
  have h := ((hasDerivAt_id s).div_const 2).const_cpow (c := (q : ℂ)) (Or.inl natCast_q_ne_zero)
  simpa using h

lemma logDeriv_qpow (s : ℂ) : logDeriv (fun s : ℂ => (q : ℂ) ^ (s / 2)) s = Real.log q / 2 := by
  rw [logDeriv_apply, (hasDerivAt_qpow s).deriv, Complex.natCast_log]
  field_simp [qpow_ne_zero s]

lemma differentiable_completedLSym (hχ1 : χ ≠ 1) : Differentiable ℂ (completedLSym χ) :=
  differentiable_qpow.mul (differentiable_completedLFunction hχ1)

lemma completedLSym_eq_zero_iff' (s : ℂ) : completedLSym χ s = 0 ↔ completedLFunction χ s = 0 := by
  unfold completedLSym
  rw [mul_eq_zero]
  simp only [qpow_ne_zero s, false_or]

lemma logDeriv_completedLSym (hχ1 : χ ≠ 1) {s : ℂ} (hΛ : completedLFunction χ s ≠ 0) :
    logDeriv (completedLSym χ) s = Real.log q / 2 + logDeriv (completedLFunction χ) s := by
  unfold completedLSym
  rw [logDeriv_mul (f := fun s : ℂ => (q : ℂ) ^ (s / 2)) (g := completedLFunction χ) s
    (qpow_ne_zero s) hΛ (differentiable_qpow s) (differentiable_completedLFunction hχ1 s), logDeriv_qpow]

/-- **Functional equation for Λ_sym**: Λ_sym(1−w,χ) = W(χ)·Λ_sym(w,χ⁻¹). -/
lemma completedLSym_one_sub (hprim : χ.IsPrimitive) (w : ℂ) :
    completedLSym χ (1 - w) = rootNumber χ * completedLSym χ⁻¹ w := by
  unfold completedLSym
  rw [hprim.completedLFunction_one_sub w]
  have hmul : (q : ℂ) ^ ((1 - w) / 2) * (q : ℂ) ^ (w - 1 / 2) = (q : ℂ) ^ (w / 2) := by
    rw [← cpow_add _ _ natCast_q_ne_zero]
    congr 1
    ring
  calc (q : ℂ) ^ ((1 - w) / 2) * ((q : ℂ) ^ (w - 1 / 2) * rootNumber χ * completedLFunction χ⁻¹ w)
      = ((q : ℂ) ^ ((1 - w) / 2) * (q : ℂ) ^ (w - 1 / 2)) * rootNumber χ
          * completedLFunction χ⁻¹ w := by ring
    _ = rootNumber χ * ((q : ℂ) ^ (w / 2) * completedLFunction χ⁻¹ w) := by rw [hmul]; ring

/-! ## Zeros and orders of Λ and Λ_sym -/

lemma completedLFunction_eq_zero_iff_of_re_pos (hq : 1 < q) {s : ℂ} (hs : 0 < s.re) :
    completedLFunction χ s = 0 ↔ χ.LFunction s = 0 := by
  have h := (completed_eq_gamma_mul_L (χ := χ) hq hs).eq_of_nhds
  obtain ⟨_, hγ⟩ := gammaFactor_analyticAt (χ := χ) hs
  rw [h, Pi.mul_apply, mul_eq_zero]
  simp [hγ]

lemma completedLFunction_ne_zero_of_one_le_re (hq : 1 < q) (hχ1 : χ ≠ 1) {s : ℂ} (hs : 1 ≤ s.re) :
    completedLFunction χ s ≠ 0 := by
  rw [Ne, completedLFunction_eq_zero_iff_of_re_pos hq (by linarith)]
  exact LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) hs

lemma completedLFunction_ne_zero_of_re_nonpos (hq : 1 < q) (hprim : χ.IsPrimitive) {s : ℂ}
    (hs : s.re ≤ 0) : completedLFunction χ s ≠ 0 := by
  have hχ1 := ne_one_of_primitive hq hprim
  have e : s = 1 - (1 - s) := by ring
  rw [e, hprim.completedLFunction_one_sub (1 - s)]
  refine mul_ne_zero (mul_ne_zero ?_ (rootNumber_ne_zero hq hprim)) ?_
  · intro h
    exact natCast_q_ne_zero (q := q) ((cpow_eq_zero_iff _ _).mp h).1
  · exact completedLFunction_ne_zero_of_one_le_re (χ := χ⁻¹) hq (inv_ne_one hχ1)
      (by simp; linarith)

/-- The zeros of Λ(·,χ) are exactly the nontrivial zeros of L(·,χ) (primitive χ mod q > 1). -/
lemma completedLFunction_eq_zero_iff (hq : 1 < q) (hprim : χ.IsPrimitive) {s : ℂ} :
    completedLFunction χ s = 0 ↔ IsNontrivialZeroL χ s := by
  have hχ1 := ne_one_of_primitive hq hprim
  constructor
  · intro h
    have h1 : 0 < s.re := by
      by_contra hle
      exact completedLFunction_ne_zero_of_re_nonpos hq hprim (not_lt.mp hle) h
    have h2 : s.re < 1 := by
      by_contra hle
      exact completedLFunction_ne_zero_of_one_le_re hq hχ1 (not_lt.mp hle) h
    exact ⟨(completedLFunction_eq_zero_iff_of_re_pos hq h1).mp h, h1, h2⟩
  · rintro ⟨hz, h1, _⟩
    exact (completedLFunction_eq_zero_iff_of_re_pos hq h1).mpr hz

lemma completedLSym_eq_zero_iff (hq : 1 < q) (hprim : χ.IsPrimitive) {s : ℂ} :
    completedLSym χ s = 0 ↔ IsNontrivialZeroL χ s := by
  rw [completedLSym_eq_zero_iff', completedLFunction_eq_zero_iff hq hprim]

/-- On Re ρ > 0 the analytic order of Λ(·,χ) equals zeroMultL χ ρ. -/
lemma analyticOrderNatAt_completedLFunction (hq : 1 < q) (hχ1 : χ ≠ 1) {ρ : ℂ} (h : 0 < ρ.re) :
    analyticOrderNatAt (completedLFunction χ) ρ = zeroMultL χ ρ := by
  have hev := completed_eq_gamma_mul_L (χ := χ) hq h
  obtain ⟨hγan, hγ0⟩ := gammaFactor_analyticAt (χ := χ) h
  have hLan : AnalyticAt ℂ χ.LFunction ρ := LFunction_analyticOnNhd hχ1 ρ (mem_univ _)
  unfold zeroMultL analyticOrderNatAt
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul hγan hLan,
    hγan.analyticOrderAt_eq_zero.mpr hγ0, zero_add]

/-- On Re ρ > 0 the analytic order of Λ_sym(·,χ) equals zeroMultL χ ρ. -/
lemma analyticOrderNatAt_completedLSym (hq : 1 < q) (hχ1 : χ ≠ 1) {ρ : ℂ} (h : 0 < ρ.re) :
    analyticOrderNatAt (completedLSym χ) ρ = zeroMultL χ ρ := by
  have hqan : AnalyticAt ℂ (fun s : ℂ => (q : ℂ) ^ (s / 2)) ρ := differentiable_qpow.analyticAt ρ
  have hΛan : AnalyticAt ℂ (completedLFunction χ) ρ :=
    (differentiable_completedLFunction hχ1).analyticAt ρ
  have hmul : completedLSym χ = (fun s : ℂ => (q : ℂ) ^ (s / 2)) * completedLFunction χ := rfl
  rw [← analyticOrderNatAt_completedLFunction hq hχ1 h]
  unfold analyticOrderNatAt
  rw [hmul, analyticOrderAt_mul hqan hΛan, hqan.analyticOrderAt_eq_zero.mpr (qpow_ne_zero ρ),
    zero_add]


/-- **Bridge for the Γ-side (GammaSideChi).** On Re s > 0 with L(s,χ) ≠ 0:
logDeriv Λ_sym(s,χ) = logDeriv L(s,χ) + logDeriv (z ↦ q^{z/2}·γ_χ(z)) (s). -/
lemma logDeriv_completedLSym_split (hq : 1 < q) (hχ1 : χ ≠ 1) {s : ℂ} (hre : 0 < s.re)
    (hL : χ.LFunction s ≠ 0) :
    logDeriv (completedLSym χ) s
      = logDeriv χ.LFunction s + logDeriv (fun z => (q : ℂ) ^ (z / 2) * gammaFactor χ z) s := by
  have hev : completedLSym χ =ᶠ[𝓝 s]
      (fun z => ((q : ℂ) ^ (z / 2) * gammaFactor χ z) * χ.LFunction z) := by
    filter_upwards [completed_eq_gamma_mul_L (χ := χ) hq hre] with z hz
    simp only [completedLSym, hz, Pi.mul_apply]
    ring
  obtain ⟨hγan, hγ0⟩ := gammaFactor_analyticAt (χ := χ) hre
  have hA : DifferentiableAt ℂ (fun z => (q : ℂ) ^ (z / 2) * gammaFactor χ z) s :=
    (differentiable_qpow s).mul hγan.differentiableAt
  have hAne : (q : ℂ) ^ (s / 2) * gammaFactor χ s ≠ 0 := mul_ne_zero (qpow_ne_zero s) hγ0
  have e1 : logDeriv (completedLSym χ) s
      = logDeriv (fun z => ((q : ℂ) ^ (z / 2) * gammaFactor χ z) * χ.LFunction z) s := by
    simp only [logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [e1, logDeriv_mul (f := fun z => (q : ℂ) ^ (z / 2) * gammaFactor χ z) (g := χ.LFunction) s
    hAne hL hA ((differentiable_LFunction hχ1) s), add_comm]

/-! ## The count -/

/-- **N_χ(T₁,T₂) as a contour integral.** For T₁ ≤ T₂ (any sign) with no nontrivial zero of
L(·,χ) of ordinate T₁ or T₂:  (1/2πi)∮_{∂([−1,2]×[T₁,T₂])} Λ_sym'/Λ_sym = NcountL χ T₁ T₂. -/
theorem rectangleIntegral'_logDeriv_completedLSym_eq_NcountL (hq : 1 < q) (hprim : χ.IsPrimitive)
    {T₁ T₂ : ℝ} (hT : T₁ ≤ T₂) (hgood₁ : ∀ ρ, IsNontrivialZeroL χ ρ → ρ.im ≠ T₁)
    (hgood₂ : ∀ ρ, IsNontrivialZeroL χ ρ → ρ.im ≠ T₂) :
    RectangleIntegral' (logDeriv (completedLSym χ)) (-1 + T₁ * I) (2 + T₂ * I)
      = (NcountL χ T₁ T₂ : ℂ) := by
  classical
  have hχ1 := ne_one_of_primitive hq hprim
  set z : ℂ := -1 + T₁ * I with hzdef
  set w : ℂ := 2 + T₂ * I with hwdef
  have hzre : z.re = -1 := by simp [z]
  have hzim : z.im = T₁ := by simp [z]
  have hwre : w.re = 2 := by simp [w]
  have hwim : w.im = T₂ := by simp [w]
  have hre : z.re ≤ w.re := by rw [hzre, hwre]; norm_num
  have him : z.im ≤ w.im := by rw [hzim, hwim]; exact hT
  have hmem : ∀ s : ℂ, s ∈ Rectangle z w ↔
      (-1 ≤ s.re ∧ s.re ≤ 2) ∧ (T₁ ≤ s.im ∧ s.im ≤ T₂) := by
    intro s
    simp only [Rectangle, mem_reProdIm, hzre, hzim, hwre, hwim,
      uIcc_of_le (show (-1 : ℝ) ≤ 2 by norm_num), uIcc_of_le hT, mem_Icc]
  have hf : AnalyticOnNhd ℂ (completedLSym χ) (Rectangle z w) := fun s _ =>
    (differentiable_completedLSym hχ1).analyticAt s
  have hg : AnalyticOnNhd ℂ (fun _ : ℂ => (1 : ℂ)) (Rectangle z w) := fun _ _ => analyticAt_const
  have hfin := (LSeam_of hq hprim).finite_window T₁ T₂
  have hZ : ∀ s ∈ Rectangle z w, completedLSym χ s = 0 ↔ s ∈ hfin.toFinset := by
    intro s hs
    rw [Set.Finite.mem_toFinset]
    obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := (hmem s).mp hs
    rw [completedLSym_eq_zero_iff hq hprim]
    constructor
    · intro hnz
      exact ⟨hnz, lt_of_le_of_ne hi1 (fun h' => hgood₁ s hnz h'.symm), hi2⟩
    · rintro ⟨hnz, _⟩
      exact hnz
  have hZsub : ((hfin.toFinset : Finset ℂ) : Set ℂ) ⊆ Rectangle z w := by
    intro s hs
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at hs
    obtain ⟨⟨_, h1, h2⟩, hi1, hi2⟩ := hs
    exact (hmem s).mpr ⟨⟨by linarith, by linarith⟩, hi1.le, hi2⟩
  have hborder : ∀ s ∈ RectangleBorder z w, completedLSym χ s ≠ 0 := by
    intro s hs h0
    obtain ⟨⟨hr1, hr2⟩, ⟨hi1, hi2⟩⟩ := (hmem s).mp (rectangleBorder_subset_rectangle z w hs)
    have hnz := (completedLSym_eq_zero_iff hq hprim).mp h0
    simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff, hzre, hzim, hwre,
      hwim] at hs
    rcases hs with ((⟨_, h'⟩ | ⟨h', _⟩) | ⟨_, h'⟩) | ⟨h', _⟩
    · exact hgood₁ s hnz h'
    · linarith [hnz.2.1]
    · exact hgood₂ s hnz h'
    · linarith [hnz.2.2]
  have key := Zeta23.Analytic.rectangleIntegral'_mul_logDeriv hre him hf hg hborder
    hfin.toFinset hZ hZsub
  simp only [one_mul, mul_one] at key
  rw [show (fun s => logDeriv (completedLSym χ) s) = logDeriv (completedLSym χ) from rfl] at key
  rw [key]
  unfold NcountL
  have hset : zerosInL χ T₁ T₂ = {ρ | IsNontrivialZeroL χ ρ} ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂} := by
    ext ρ; simp [zerosInL]
  rw [hset, finsum_mem_eq_finite_toFinset_sum _ hfin, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun ρ hρ => ?_)
  rw [Set.Finite.mem_toFinset] at hρ
  obtain ⟨⟨_, h1, _⟩, _⟩ := hρ
  rw [analyticOrderNatAt_completedLSym hq hχ1 h1]

end ThmE
end Zeta23
