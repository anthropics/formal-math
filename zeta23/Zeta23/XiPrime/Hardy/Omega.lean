/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Hardy/Omega.lean — the completed object Ω := Γℝ·W.

W(s) = −χ(s)W(1−s) with χ = Γℝ(1−s)/Γℝ(s) says exactly that Ω(s) := Γℝ(s)·W(s) is ODD under s ↦ 1−s off the real
axis: Ω(1−s) = −Ω(s); also Ω(s̄) = conj Ω(s).  So Ω plays for W the role ξ′ plays for itself in
Zeta23/XiPrime/ZeroCount/Contour.lean: logDeriv Ω (1−s̄) = −conj logDeriv Ω (s) (the fold), Ω is analytic off ℝ with the
same zeros and orders as W there, and logDeriv Ω = Γℝ′/Γℝ + W′/W (the split; Γℝ′/Γℝ gives the main term).
-/
import Zeta23.XiPrime.Hardy.Seam

open Complex Set Filter Topology Metric
open scoped ComplexConjugate

noncomputable section

namespace Zeta23
namespace XiPrime
namespace Hardy

/-- Ω := Γℝ · W. -/
def omegaW (s : ℂ) : ℂ := Gammaℝ s * hardyW s

lemma omegaW_def (s : ℂ) : omegaW s = Gammaℝ s * hardyW s := rfl

theorem omegaW_analyticAt {s : ℂ} (hs : s.im ≠ 0) : AnalyticAt ℂ omegaW s :=
  (analyticAt_Gammaℝ_of_im_ne_zero hs).mul (hardyW_analyticAt hs)

theorem omegaW_analyticOnNhd {U : Set ℂ} (hU : U ⊆ {s : ℂ | s.im ≠ 0}) : AnalyticOnNhd ℂ omegaW U :=
  fun _ hs => omegaW_analyticAt (hU hs)

theorem omegaW_eq_zero_iff {s : ℂ} (hs : s.im ≠ 0) : omegaW s = 0 ↔ hardyW s = 0 := by
  rw [omegaW, mul_eq_zero]; exact ⟨fun h => h.resolve_left (Gammaℝ_ne_zero_of_im_ne_zero hs), Or.inr⟩

/-- Ω and W have the same order at non-real points. -/
theorem analyticOrderAt_omegaW {s : ℂ} (hs : s.im ≠ 0) : analyticOrderAt omegaW s = analyticOrderAt hardyW s := by
  have h0 : analyticOrderAt Gammaℝ s = 0 :=
    (analyticAt_Gammaℝ_of_im_ne_zero hs).analyticOrderAt_eq_zero.mpr (Gammaℝ_ne_zero_of_im_ne_zero hs)
  have e : omegaW = Gammaℝ * hardyW := funext fun z => rfl
  rw [e, analyticOrderAt_mul (analyticAt_Gammaℝ_of_im_ne_zero hs) (hardyW_analyticAt hs), h0, zero_add]

theorem analyticOrderNatAt_omegaW {s : ℂ} (hs : s.im ≠ 0) : analyticOrderNatAt omegaW s = wMult s := by
  unfold analyticOrderNatAt wMult; rw [analyticOrderAt_omegaW hs]

/-- **Ω(1−s) = −Ω(s)** off the real axis. -/
theorem omegaW_one_sub {s : ℂ} (hs : s.im ≠ 0) : omegaW (1 - s) = -omegaW s := by
  have hs' := im_one_sub_ne_zero hs
  rw [omegaW, omegaW, hardyW_eq_neg_chiFE_mul hs, chiFE_def]
  field_simp [Gammaℝ_ne_zero_of_im_ne_zero hs]

theorem omegaW_conj {s : ℂ} (hs : s.im ≠ 0) : omegaW (conj s) = conj (omegaW s) := by
  rw [omegaW, omegaW, Zeta23.RvM.Gammaℝ_conj, hardyW_conj hs, map_mul]

theorem omegaW_differentiableAt {s : ℂ} (hs : s.im ≠ 0) : DifferentiableAt ℂ omegaW s :=
  (omegaW_analyticAt hs).differentiableAt

/-- Ω′(1−s) = Ω′(s). -/
theorem deriv_omegaW_one_sub {s : ℂ} (hs : s.im ≠ 0) : deriv omegaW (1 - s) = deriv omegaW s := by
  have hev : omegaW =ᶠ[𝓝 s] fun z => -omegaW (1 - z) := by
    filter_upwards [isOpen_im_ne_zero.mem_nhds hs] with z hz
    rw [omegaW_one_sub hz]; ring
  rw [hev.deriv_eq]
  have hd : DifferentiableAt ℂ omegaW (1 - s) := omegaW_differentiableAt (im_one_sub_ne_zero hs)
  have h1 : deriv (fun z => omegaW (1 - z)) s = -deriv omegaW (1 - s) := by
    rw [deriv_comp_const_sub]
  have h2 : deriv (fun z => -omegaW (1 - z)) s = -deriv (fun z => omegaW (1 - z)) s :=
    deriv.neg (f := fun z => omegaW (1 - z))
  rw [h2, h1]; ring

theorem deriv_omegaW_conj {s : ℂ} (hs : s.im ≠ 0) : deriv omegaW (conj s) = conj (deriv omegaW s) := by
  refine deriv_conj_of_symm (omegaW_differentiableAt hs) ?_
  have hs' : (conj s).im ≠ 0 := by simpa using hs
  filter_upwards [isOpen_im_ne_zero.mem_nhds hs'] with z hz
  exact omegaW_conj hz

theorem logDeriv_omegaW_one_sub {s : ℂ} (hs : s.im ≠ 0) : logDeriv omegaW (1 - s) = -logDeriv omegaW s := by
  rw [logDeriv_apply, logDeriv_apply, deriv_omegaW_one_sub hs, omegaW_one_sub hs, div_neg]

theorem logDeriv_omegaW_conj {s : ℂ} (hs : s.im ≠ 0) :
    logDeriv omegaW (conj s) = conj (logDeriv omegaW s) := by
  rw [logDeriv_apply, logDeriv_apply, deriv_omegaW_conj hs, omegaW_conj hs, map_div₀]

/-- **the fold identity**: logDeriv Ω (1 − s̄) = −conj (logDeriv Ω s) off the real axis. -/
theorem logDeriv_omegaW_one_sub_conj {s : ℂ} (hs : s.im ≠ 0) :
    logDeriv omegaW (1 - conj s) = -conj (logDeriv omegaW s) := by
  have hs' : (conj s).im ≠ 0 := by simpa using hs
  rw [logDeriv_omegaW_one_sub hs', logDeriv_omegaW_conj hs]

/-- **the split**: logDeriv Ω = Γℝ′/Γℝ + W′/W where W ≠ 0 (off the real axis). -/
theorem logDeriv_omegaW_eq {s : ℂ} (hs : s.im ≠ 0) (hW : hardyW s ≠ 0) :
    logDeriv omegaW s = logDeriv Gammaℝ s + logDeriv hardyW s := by
  have e : omegaW = fun z => Gammaℝ z * hardyW z := funext fun z => rfl
  rw [e, logDeriv_mul s (Gammaℝ_ne_zero_of_im_ne_zero hs) hW (differentiableAt_Gammaℝ_of_im_ne_zero hs)
    (hardyW_differentiableAt hs)]

end Hardy
end XiPrime
end Zeta23

end
