/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmE/GammaSideChi.lean — the Γ/conductor side of the folded contour
for L(s,χ) is EXACTLY ∫ μ_χ:
  (1/π)·Im ∫_L logDeriv(arch) = ∫_{T₁}^{T₂} μ_χ(t) dt,   arch(s) := q^{s/2} · Γℝ(s + κ),
where κ ∈ {0,1} is the parity (gammaFactor χ s = Γℝ(s + κ) by Even/Odd.gammaFactor_def), because
logDeriv arch = (log q)/2 + logDeriv Γℝ(·+κ) is holomorphic on Re s > 0 and on the critical line
  Re[(log q)/2 − (log π)/2 + ψ(¼ + κ/2 + it/2)/2] = π·μ_χ(t)   (μ_χ = Zeta23.ThmE.muq κ q).
This is the analogue of Zeta23/RvM/GammaSide.lean for L(s,χ).
-/
import Zeta23.ThmE.Hypotheses
import Zeta23.RvM.GammaSide
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

open Complex MeasureTheory Set Zeta23.RvM
open scoped Interval

noncomputable section

namespace Zeta23
namespace ThmE

variable (q κ : ℕ) [NeZero q]

/-- the archimedean factor carrying the conductor: arch(s) := q^{s/2}·Γℝ(s+κ). -/
def archChi (s : ℂ) : ℂ := (q : ℂ) ^ (s / 2) * Complex.Gammaℝ (s + κ)

lemma q_cpow_ne_zero (s : ℂ) : (q : ℂ) ^ (s / 2) ≠ 0 := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q)).ne'
  simp [Complex.cpow_eq_zero_iff, hq0]

lemma archChi_differentiableOn :
    DifferentiableOn ℂ (archChi q κ) rightHalfPlane := by
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  have h1 : DifferentiableAt ℂ (fun s : ℂ => (q : ℂ) ^ (s / 2)) s := by
    apply DifferentiableAt.const_cpow (by fun_prop)
    exact Or.inl (by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q)).ne')
  have h2 : DifferentiableAt ℂ (fun s : ℂ => Complex.Gammaℝ (s + κ)) s := by
    have hre : 0 < (s + (κ:ℂ)).re := by
      have : (0:ℝ) ≤ κ := Nat.cast_nonneg κ
      have hs' : 0 < s.re := hs
      simp only [Complex.add_re, Complex.natCast_re]
      linarith
    have hG : DifferentiableAt ℂ Complex.Gammaℝ (s + κ) :=
      (Gammaℝ_differentiableOn (s + κ) hre).differentiableAt
        (isOpen_rightHalfPlane.mem_nhds hre)
    have haff : DifferentiableAt ℂ (fun z : ℂ => z + (κ:ℂ)) s := by fun_prop
    have hcomp : DifferentiableAt ℂ (Complex.Gammaℝ ∘ fun z : ℂ => z + (κ:ℂ)) s :=
      DifferentiableAt.comp s hG haff
    exact hcomp
  exact h1.mul h2

lemma archChi_ne_zero {s : ℂ} (hs : 0 < s.re) : archChi q κ s ≠ 0 := by
  unfold archChi
  apply mul_ne_zero (q_cpow_ne_zero q s)
  apply Complex.Gammaℝ_ne_zero_of_re_pos
  simp only [Complex.add_re, Complex.natCast_re]
  have : (0:ℝ) ≤ κ := Nat.cast_nonneg κ
  linarith

lemma logDeriv_archChi_differentiableOn :
    DifferentiableOn ℂ (logDeriv (archChi q κ)) rightHalfPlane := by
  have hA : AnalyticOnNhd ℂ (archChi q κ) rightHalfPlane :=
    (archChi_differentiableOn q κ).analyticOnNhd isOpen_rightHalfPlane
  have : logDeriv (archChi q κ) = fun s => deriv (archChi q κ) s / archChi q κ s := by
    funext s; rfl
  rw [this]
  exact hA.deriv.differentiableOn.div hA.differentiableOn fun s hs => archChi_ne_zero q κ hs

/-- logDeriv arch(s) = (log q)/2 + (−(log π)/2 + ψ((s+κ)/2)/2) on Re s > 0. -/
theorem logDeriv_archChi {s : ℂ} (hs : 0 < s.re) :
    logDeriv (archChi q κ) s = (Real.log q : ℂ) / 2 +
      (-(Real.log Real.pi : ℂ) / 2 + (1/2 : ℂ) * Complex.digamma ((s + κ) / 2)) := by
  have hκre : 0 < (s + (κ:ℂ)).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    have : (0:ℝ) ≤ κ := Nat.cast_nonneg κ
    linarith
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q)).ne'
  have e : archChi q κ = fun s : ℂ => (q : ℂ) ^ (s / 2) * Complex.Gammaℝ (s + κ) := rfl
  have hf : (fun s : ℂ => (q : ℂ) ^ (s / 2)) s ≠ 0 := q_cpow_ne_zero q s
  have hg : (fun s : ℂ => Complex.Gammaℝ (s + κ)) s ≠ 0 := by
    apply Complex.Gammaℝ_ne_zero_of_re_pos hκre
  have hdf : DifferentiableAt ℂ (fun s : ℂ => (q : ℂ) ^ (s / 2)) s :=
    DifferentiableAt.const_cpow (by fun_prop) (Or.inl hq0)
  have hdg : DifferentiableAt ℂ (fun s : ℂ => Complex.Gammaℝ (s + κ)) s := by
    have hG : DifferentiableAt ℂ Complex.Gammaℝ (s + κ) :=
      (Gammaℝ_differentiableOn (s + κ) hκre).differentiableAt
        (isOpen_rightHalfPlane.mem_nhds hκre)
    have haff : DifferentiableAt ℂ (fun z : ℂ => z + (κ:ℂ)) s := by fun_prop
    have hcomp : DifferentiableAt ℂ (Complex.Gammaℝ ∘ fun z : ℂ => z + (κ:ℂ)) s :=
      DifferentiableAt.comp s hG haff
    exact hcomp
  rw [e, logDeriv_mul (f := fun s : ℂ => (q : ℂ) ^ (s / 2))
    (g := fun s : ℂ => Complex.Gammaℝ (s + κ)) s hf hg hdf hdg]
  have h1 : logDeriv (fun s : ℂ => (q : ℂ) ^ (s / 2)) s = (Real.log q : ℂ) / 2 := by
    have hder : HasDerivAt (fun s : ℂ => (q : ℂ) ^ (s / 2))
        ((q : ℂ) ^ (s / 2) * Complex.log q * (1 / 2)) s := by
      have hd : HasDerivAt (fun s : ℂ => s / 2) (1 / 2 : ℂ) s := by
        simpa using (hasDerivAt_id s).div_const (2:ℂ)
      exact hd.const_cpow (Or.inl hq0)
    rw [logDeriv_apply, hder.deriv]
    have hne : (q : ℂ) ^ (s / 2) ≠ 0 := q_cpow_ne_zero q s
    have hlogq : Complex.log (q : ℂ) = (Real.log q : ℂ) := by
      rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg q)]
    rw [hlogq, mul_assoc, mul_div_cancel_left₀ _ hne]
    ring
  have h2 : logDeriv (fun s : ℂ => Complex.Gammaℝ (s + κ)) s =
      -(Real.log Real.pi : ℂ) / 2 + (1/2 : ℂ) * Complex.digamma ((s + κ) / 2) := by
    have hshift : AnalyticAt ℂ (fun s : ℂ => s + (κ:ℂ)) s := by fun_prop
    have hGd : DifferentiableAt ℂ Complex.Gammaℝ ((fun s : ℂ => s + (κ:ℂ)) s) :=
      (Gammaℝ_differentiableOn (s + κ) hκre).differentiableAt
        (isOpen_rightHalfPlane.mem_nhds hκre)
    have := logDeriv_comp (f := Complex.Gammaℝ) (g := fun s : ℂ => s + (κ:ℂ)) (x := s)
      hGd (by fun_prop)
    rw [show (Complex.Gammaℝ ∘ fun s : ℂ => s + (κ:ℂ)) = fun s => Complex.Gammaℝ (s + κ) from rfl]
      at this
    rw [this, RvM.logDeriv_Gammaℝ hκre]
    have : deriv (fun s : ℂ => s + (κ:ℂ)) s = 1 := by
      rw [deriv_add_const, deriv_id'']
    rw [this]; ring
  rw [h1, h2]

/-- Re logDeriv arch(½+it) = π·μ_χ(t). -/
theorem re_logDeriv_archChi_half (t : ℝ) :
    (logDeriv (archChi q κ) (1/2 + t * I)).re = Real.pi * muq κ q t := by
  rw [logDeriv_archChi q κ (by simp)]
  have harg : ((1:ℂ)/2 + t * I + κ) / 2 = 1/4 + (κ:ℂ)/2 + Complex.I * t / 2 := by ring
  rw [harg, muq]
  have hq1 : (1 ≤ q) := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq0 : ((q:ℝ)) ≠ 0 := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q)).ne'
  have hlogdiv : Real.log ((q : ℝ) / Real.pi) = Real.log q - Real.log Real.pi :=
    Real.log_div hq0 Real.pi_ne_zero
  simp only [Complex.add_re, Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.ofReal_re,
    Complex.neg_re, Complex.mul_re, Complex.one_re, Complex.one_im]
  rw [hlogdiv]
  field_simp
  ring

/-- the Γ/conductor-side contour identity: for 0 < T₁, T₂,
(1/π)·Im(halfContour (logDeriv arch) T₁ T₂) = ∫_{T₁}^{T₂} μ_χ. -/
theorem gammaSideChi {T₁ T₂ : ℝ} (_h0 : 0 < T₁) (_h0' : 0 < T₂) :
    (1 / Real.pi) * (RvM.halfContour (logDeriv (archChi q κ)) T₁ T₂).im =
      ∫ t in T₁..T₂, muq κ q t := by
  set F := logDeriv (archChi q κ) with hF
  have hrect : (Set.uIcc (1/2:ℝ) 2 ×ℂ Set.uIcc T₁ T₂) ⊆ rightHalfPlane := by
    rintro s ⟨hre, -⟩
    rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 2)] at hre
    show 0 < s.re
    have := hre.1
    linarith [this]
  have hCG := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F (1/2 + T₁ * I)
    (2 + T₂ * I) ((logDeriv_archChi_differentiableOn q κ).mono (by simpa using hrect))
  simp only [add_re, one_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, one_im, mul_im, zero_add, div_ofNat_re, div_ofNat_im, zero_div,
    re_ofNat, im_ofNat] at hCG
  have hhc : RvM.halfContour F T₁ T₂ = I * ∫ y : ℝ in T₁..T₂, F (1/2 + y * I) := by
    unfold RvM.halfContour
    have hthis := hCG
    simp only [smul_eq_mul] at hthis
    have hc : ((1/2 : ℝ) : ℂ) = (1/2 : ℂ) := by norm_num
    simp only [hc] at hthis
    linear_combination hthis
  rw [hhc, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
  have hcont : Continuous fun y : ℝ => F (1/2 + y * I) := by
    have hd := logDeriv_archChi_differentiableOn q κ
    have hmap : Continuous fun y : ℝ => ((1:ℂ)/2 + y * I) := by fun_prop
    refine (hd.continuousOn.comp_continuous hmap fun y => ?_)
    show 0 < ((1:ℂ)/2 + y * I).re
    simp
  rw [show ((∫ y : ℝ in T₁..T₂, F (1/2 + y * I)).re) = ∫ y : ℝ in T₁..T₂, (F (1/2 + y * I)).re from
    (Complex.reCLM.intervalIntegral_comp_comm (hcont.intervalIntegrable _ _)).symm]
  simp_rw [hF, re_logDeriv_archChi_half]
  rw [intervalIntegral.integral_const_mul]
  field_simp

end ThmE
end Zeta23
