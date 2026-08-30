/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Hardy/Basic.lean — analytic facts about χ, L₂ and W := ζ′ − ½(χ′/χ)ζ OFF THE REAL AXIS
(W zero side; [XF′ §9.0–9.1 (Z2)]).

Everything here is at points s with Im s ≠ 0, where Γℝ(s), Γℝ(1−s) are analytic and nonzero, ζ, ζ′ are analytic
(s ≠ 1), hence χ = Γℝ(1−s)/Γℝ(s) is an analytic unit, L₂ = −½ χ′/χ = ½[(Γℝ′/Γℝ)(s) + (Γℝ′/Γℝ)(1−s)] is analytic,
and W = ζ′ + L₂ζ is analytic.  Exports: ζ(s) = χ(s)ζ(1−s) (zeta_eq_chiFE_mul); L₂(1−s) = L₂(s), L₂(s̄) = conj L₂(s);
W(s̄) = conj W(s); the functional equation **W(s) = −χ(s)·W(1−s)**; hence IsWZero (reflect ρ) ↔ IsWZero ρ and
analyticOrderAt hardyW (reflect ρ) = analyticOrderAt hardyW ρ.
-/
import Zeta23.XiPrime.Statement
import Zeta23.ZetaReflect
import Zeta23.RvM.Fold
import Zeta23.RvM.GammaSide
import Zeta23.RvM.CountByIntegral
import Zeta23.WeilEF.XiLogDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Shift

open Complex Set Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Zeta23
namespace XiPrime
namespace Hardy

/-! ### §1. Γℝ off the real axis -/

lemma ne_neg_nat_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) (m : ℕ) : s ≠ -(m : ℂ) := by
  intro h; apply hs; rw [h]; simp

lemma ne_one_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) : s ≠ 1 := by
  intro h; apply hs; rw [h]; simp

lemma ne_zero_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) : s ≠ 0 := by
  intro h; apply hs; rw [h]; simp

lemma im_one_sub_ne_zero {s : ℂ} (hs : s.im ≠ 0) : (1 - s).im ≠ 0 := by
  simpa using hs

lemma half_ne_neg_nat {s : ℂ} (hs : s.im ≠ 0) (m : ℕ) : s / 2 ≠ -(m : ℂ) := by
  intro h; apply hs
  have : (s / 2).im = 0 := by rw [h]; simp
  simpa using this

lemma Gammaℝ_ne_zero_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) : Gammaℝ s ≠ 0 := by
  rw [Ne, Gammaℝ_eq_zero_iff, not_exists]
  intro n h; apply hs; rw [h]; simp

/-- Γℝ is complex-differentiable at every non-real point. -/
lemma differentiableAt_Gammaℝ_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) : DifferentiableAt ℂ Gammaℝ s := by
  have h1 : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s := by
    refine DifferentiableAt.const_cpow ?_ (Or.inl (by exact_mod_cast Real.pi_ne_zero))
    exact (differentiableAt_id.neg).div_const 2
  have h2 : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s :=
    (Complex.differentiableAt_Gamma _ (half_ne_neg_nat hs)).comp s (differentiableAt_id.div_const 2)
  have : Gammaℝ = fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2) := funext Gammaℝ_def
  rw [this]; exact h1.mul h2

lemma isOpen_im_ne_zero : IsOpen {s : ℂ | s.im ≠ 0} := isOpen_ne_fun Complex.continuous_im continuous_const

lemma analyticAt_Gammaℝ_of_im_ne_zero {s : ℂ} (hs : s.im ≠ 0) : AnalyticAt ℂ Gammaℝ s := by
  refine Complex.analyticAt_iff_eventually_differentiableAt.mpr ?_
  filter_upwards [isOpen_im_ne_zero.mem_nhds hs] with z hz
  exact differentiableAt_Gammaℝ_of_im_ne_zero hz

lemma analyticAt_Gammaℝ_one_sub {s : ℂ} (hs : s.im ≠ 0) : AnalyticAt ℂ (fun z => Gammaℝ (1 - z)) s :=
  (analyticAt_Gammaℝ_of_im_ne_zero (im_one_sub_ne_zero hs)).comp (analyticAt_const.sub analyticAt_id)

/-! ### §2. χ and L₂ -/

lemma chiFE_def (s : ℂ) : chiFE s = Gammaℝ (1 - s) / Gammaℝ s := rfl

lemma chiFE_analyticAt {s : ℂ} (hs : s.im ≠ 0) : AnalyticAt ℂ chiFE s := by
  have : chiFE = fun z => Gammaℝ (1 - z) / Gammaℝ z := funext chiFE_def
  rw [this]
  exact (analyticAt_Gammaℝ_one_sub hs).div (analyticAt_Gammaℝ_of_im_ne_zero hs)
    (Gammaℝ_ne_zero_of_im_ne_zero hs)

lemma chiFE_ne_zero {s : ℂ} (hs : s.im ≠ 0) : chiFE s ≠ 0 :=
  div_ne_zero (Gammaℝ_ne_zero_of_im_ne_zero (im_one_sub_ne_zero hs)) (Gammaℝ_ne_zero_of_im_ne_zero hs)

lemma chiFE_mul_chiFE_one_sub {s : ℂ} (hs : s.im ≠ 0) : chiFE s * chiFE (1 - s) = 1 := by
  rw [chiFE_def, chiFE_def, sub_sub_cancel]
  field_simp [Gammaℝ_ne_zero_of_im_ne_zero hs, Gammaℝ_ne_zero_of_im_ne_zero (im_one_sub_ne_zero hs)]

/-- logDeriv χ = −(Γℝ′/Γℝ)(1−s) − (Γℝ′/Γℝ)(s). -/
lemma logDeriv_chiFE {s : ℂ} (hs : s.im ≠ 0) :
    logDeriv chiFE s = -(logDeriv Gammaℝ (1 - s)) - logDeriv Gammaℝ s := by
  have hG := Gammaℝ_ne_zero_of_im_ne_zero hs
  have hG1 := Gammaℝ_ne_zero_of_im_ne_zero (im_one_sub_ne_zero hs)
  have e : chiFE = fun z => Gammaℝ (1 - z) / Gammaℝ z := funext chiFE_def
  have hd1 : DifferentiableAt ℂ (fun z : ℂ => Gammaℝ (1 - z)) s :=
    (differentiableAt_Gammaℝ_of_im_ne_zero (im_one_sub_ne_zero hs)).comp s
      ((differentiableAt_const (1:ℂ)).sub differentiableAt_id)
  rw [e, logDeriv_div _ (by simpa using hG1) hG hd1 (differentiableAt_Gammaℝ_of_im_ne_zero hs)]
  congr 1
  -- logDeriv (Γℝ ∘ (1 − ·)) s = −(logDeriv Γℝ)(1 − s)
  rw [logDeriv_apply, logDeriv_apply]
  have : deriv (fun z => Gammaℝ (1 - z)) s = -deriv Gammaℝ (1 - s) := by
    rw [deriv_comp_const_sub]
  rw [this]; ring

/-- **L₂ = ½[(Γℝ′/Γℝ)(s) + (Γℝ′/Γℝ)(1−s)]** off the real axis. -/
theorem L2_eq {s : ℂ} (hs : s.im ≠ 0) : L2 s = (logDeriv Gammaℝ s + logDeriv Gammaℝ (1 - s)) / 2 := by
  rw [L2, logDeriv_chiFE hs]; ring

theorem L2_one_sub {s : ℂ} (hs : s.im ≠ 0) : L2 (1 - s) = L2 s := by
  rw [L2_eq hs, L2_eq (im_one_sub_ne_zero hs), sub_sub_cancel]; ring

theorem L2_conj {s : ℂ} (hs : s.im ≠ 0) : L2 (conj s) = conj (L2 s) := by
  have hs' : (conj s).im ≠ 0 := by simpa using hs
  rw [L2_eq hs', L2_eq hs, map_div₀, map_add, ← Zeta23.RvM.logDeriv_Gammaℝ_conj,
    ← Zeta23.RvM.logDeriv_Gammaℝ_conj, map_sub, map_one, map_ofNat]

theorem L2_analyticAt {s : ℂ} (hs : s.im ≠ 0) : AnalyticAt ℂ L2 s := by
  have e : L2 = fun z => -(1/2) * (deriv chiFE z / chiFE z) := by
    funext z; rw [L2, logDeriv_apply]
  rw [e]
  exact analyticAt_const.mul ((chiFE_analyticAt hs).deriv.div (chiFE_analyticAt hs) (chiFE_ne_zero hs))

/-- χ′ = −2·L₂·χ. -/
theorem deriv_chiFE {s : ℂ} (hs : s.im ≠ 0) : deriv chiFE s = -2 * L2 s * chiFE s := by
  have h : L2 s = -(1/2) * (deriv chiFE s / chiFE s) := by rw [L2, logDeriv_apply]
  rw [h]; field_simp [chiFE_ne_zero hs]

/-! ### §3. ζ(s) = χ(s)·ζ(1−s) off the real axis -/

theorem zeta_eq_chiFE_mul {s : ℂ} (hs : s.im ≠ 0) :
    riemannZeta s = chiFE s * riemannZeta (1 - s) := by
  have hs0 := ne_zero_of_im_ne_zero hs
  have hs1' : (1 - s) ≠ 0 := sub_ne_zero.mpr (ne_one_of_im_ne_zero hs).symm
  have hG := Gammaℝ_ne_zero_of_im_ne_zero hs
  have hG1 := Gammaℝ_ne_zero_of_im_ne_zero (im_one_sub_ne_zero hs)
  have h1 := Zeta23.RvM.completedRiemannZeta_eq_Gammaℝ_mul hs0 hG
  have h2 := Zeta23.RvM.completedRiemannZeta_eq_Gammaℝ_mul hs1' hG1
  have hΛ : completedRiemannZeta (1 - s) = completedRiemannZeta s := completedRiemannZeta_one_sub s
  -- Γℝ(s)ζ(s) = Λ(s) = Λ(1−s) = Γℝ(1−s)ζ(1−s)
  rw [chiFE_def]
  field_simp
  rw [h1, h2] at *
  linear_combination -hΛ

/-! ### §4. W off the real axis: analyticity, Schwarz reflection, the functional equation -/

lemma isOpen_ne_one : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton

lemma analyticAt_riemannZeta {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s := by
  refine Complex.analyticAt_iff_eventually_differentiableAt.mpr ?_
  filter_upwards [isOpen_ne_one.mem_nhds hs] with z hz
  exact differentiableAt_riemannZeta hz

lemma analyticAt_deriv_riemannZeta {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ (deriv riemannZeta) s :=
  (analyticAt_riemannZeta hs).deriv

/-- W is analytic at every non-real point. -/
theorem hardyW_analyticAt {s : ℂ} (hs : s.im ≠ 0) : AnalyticAt ℂ hardyW s := by
  have e : hardyW = fun z => deriv riemannZeta z + L2 z * riemannZeta z := funext fun z => rfl
  rw [e]
  exact (analyticAt_deriv_riemannZeta (ne_one_of_im_ne_zero hs)).add
    ((L2_analyticAt hs).mul (analyticAt_riemannZeta (ne_one_of_im_ne_zero hs)))

theorem hardyW_differentiableAt {s : ℂ} (hs : s.im ≠ 0) : DifferentiableAt ℂ hardyW s :=
  (hardyW_analyticAt hs).differentiableAt

theorem hardyW_analyticOnNhd : AnalyticOnNhd ℂ hardyW {s : ℂ | s.im ≠ 0} := fun _ hs => hardyW_analyticAt hs

/-- generic: a derivative inherits Schwarz reflection symmetry (local version). -/
lemma deriv_conj_of_symm {f : ℂ → ℂ} {s : ℂ} (hd : DifferentiableAt ℂ f s)
    (h : ∀ᶠ z in 𝓝 (conj s), f (conj z) = conj (f z)) : deriv f (conj s) = conj (deriv f s) := by
  have h1 : HasDerivAt (fun z => conj (f (conj z))) (conj (deriv f s)) (conj s) :=
    hd.hasDerivAt.conj_conj
  have h2 : (fun z => conj (f (conj z))) =ᶠ[𝓝 (conj s)] f := by
    filter_upwards [h] with z hz
    rw [hz, Complex.conj_conj]
  exact (h1.congr_of_eventuallyEq h2.symm).deriv

lemma deriv_riemannZeta_conj {s : ℂ} (hs : s ≠ 1) :
    deriv riemannZeta (conj s) = conj (deriv riemannZeta s) := by
  refine deriv_conj_of_symm (differentiableAt_riemannZeta hs) ?_
  have hs' : conj s ≠ 1 := by
    intro h; apply hs; rw [← Complex.conj_conj s, h, map_one]
  filter_upwards [isOpen_ne_one.mem_nhds hs'] with z hz
  exact Zeta23.riemannZeta_conj (Set.mem_compl_singleton_iff.mp hz)

/-- **W(s̄) = conj W(s)** off the real axis. -/
theorem hardyW_conj {s : ℂ} (hs : s.im ≠ 0) : hardyW (conj s) = conj (hardyW s) := by
  have hs1 := ne_one_of_im_ne_zero hs
  show deriv riemannZeta (conj s) + L2 (conj s) * riemannZeta (conj s) = _
  rw [deriv_riemannZeta_conj hs1, L2_conj hs, Zeta23.riemannZeta_conj hs1, hardyW, map_add, map_mul]

/-- ζ′(s) = χ′(s)ζ(1−s) − χ(s)ζ′(1−s) off the real axis. -/
theorem deriv_riemannZeta_eq {s : ℂ} (hs : s.im ≠ 0) :
    deriv riemannZeta s = deriv chiFE s * riemannZeta (1 - s) - chiFE s * deriv riemannZeta (1 - s) := by
  have hev : riemannZeta =ᶠ[𝓝 s] fun z => chiFE z * riemannZeta (1 - z) := by
    filter_upwards [isOpen_im_ne_zero.mem_nhds hs] with z hz
    exact zeta_eq_chiFE_mul hz
  rw [hev.deriv_eq]
  have h1 : HasDerivAt chiFE (deriv chiFE s) s := (chiFE_analyticAt hs).differentiableAt.hasDerivAt
  have hz1 : (1 - s) ≠ 1 := by
    intro h; apply hs; have : s = 0 := by linear_combination -h
    rw [this]; simp
  have h2 : HasDerivAt (fun z => riemannZeta (1 - z)) (-deriv riemannZeta (1 - s)) s := by
    have hd : HasDerivAt riemannZeta (deriv riemannZeta (1 - s)) (1 - s) :=
      (differentiableAt_riemannZeta hz1).hasDerivAt
    have := hd.comp s ((hasDerivAt_const s (1:ℂ)).sub (hasDerivAt_id s))
    simpa [Function.comp_def] using this
  have h : HasDerivAt (fun z => chiFE z * riemannZeta (1 - z))
      (deriv chiFE s * riemannZeta (1 - s) + chiFE s * -deriv riemannZeta (1 - s)) s := h1.mul h2
  rw [h.deriv]; ring

/-- **The functional equation W(s) = −χ(s)·W(1−s)** off the real axis  [XF′ (Z2)]. -/
theorem hardyW_eq_neg_chiFE_mul {s : ℂ} (hs : s.im ≠ 0) : hardyW s = -chiFE s * hardyW (1 - s) := by
  have hs' := im_one_sub_ne_zero hs
  rw [hardyW, hardyW, deriv_riemannZeta_eq hs, deriv_chiFE hs, zeta_eq_chiFE_mul hs, L2_one_sub hs]
  ring

theorem hardyW_one_sub_eq_zero_iff {s : ℂ} (hs : s.im ≠ 0) : hardyW (1 - s) = 0 ↔ hardyW s = 0 := by
  rw [hardyW_eq_neg_chiFE_mul hs, mul_eq_zero, neg_eq_zero]
  exact ⟨fun h => Or.inr h, fun h => h.resolve_left (chiFE_ne_zero hs)⟩

theorem hardyW_conj_eq_zero_iff {s : ℂ} (hs : s.im ≠ 0) : hardyW (conj s) = 0 ↔ hardyW s = 0 := by
  rw [hardyW_conj hs, map_eq_zero]

/-- the non-real zeros of W are invariant under ρ ↦ 1 − ρ̄. -/
theorem isWZero_reflect_iff (ρ : ℂ) : IsWZero (reflect ρ) ↔ IsWZero ρ := by
  unfold IsWZero reflect
  constructor
  · rintro ⟨h0, him⟩
    have him' : ρ.im ≠ 0 := by simpa using him
    have hc : (conj ρ).im ≠ 0 := by simpa using him'
    exact ⟨(hardyW_conj_eq_zero_iff him').mp ((hardyW_one_sub_eq_zero_iff hc).mp h0), him'⟩
  · rintro ⟨h0, him⟩
    have hc : (conj ρ).im ≠ 0 := by simpa using him
    exact ⟨(hardyW_one_sub_eq_zero_iff hc).mpr ((hardyW_conj_eq_zero_iff him).mpr h0), by simpa using him⟩

/-! ### §5. The analytic order of W under the two symmetries -/

theorem analyticOrderAt_hardyW_one_sub {w : ℂ} (hw : w.im ≠ 0) :
    analyticOrderAt hardyW (1 - w) = analyticOrderAt hardyW w := by
  have hg : AnalyticAt ℂ (fun z : ℂ => 1 - z) w := analyticAt_const.sub analyticAt_id
  have hg' : deriv (fun z : ℂ => 1 - z) w ≠ 0 := by rw [deriv_const_sub]; simp
  -- W(1−z) = −χ(z)⁻¹·W(z) near w
  have hev : (hardyW ∘ fun z : ℂ => 1 - z) =ᶠ[𝓝 w] (fun z => -(chiFE z)⁻¹) * hardyW := by
    filter_upwards [isOpen_im_ne_zero.mem_nhds hw] with z hz
    simp only [Function.comp_apply, Pi.mul_apply]
    rw [hardyW_eq_neg_chiFE_mul hz]
    field_simp [chiFE_ne_zero hz]
  have hu : AnalyticAt ℂ (fun z => -(chiFE z)⁻¹) w := ((chiFE_analyticAt hw).inv (chiFE_ne_zero hw)).neg
  have hu0 : analyticOrderAt (fun z => -(chiFE z)⁻¹) w = 0 :=
    hu.analyticOrderAt_eq_zero.mpr (neg_ne_zero.mpr (inv_ne_zero (chiFE_ne_zero hw)))
  calc analyticOrderAt hardyW (1 - w)
      = analyticOrderAt (hardyW ∘ fun z : ℂ => 1 - z) w := by
        rw [analyticOrderAt_comp_of_deriv_ne_zero hg hg']
    _ = analyticOrderAt ((fun z => -(chiFE z)⁻¹) * hardyW) w := analyticOrderAt_congr hev
    _ = analyticOrderAt (fun z => -(chiFE z)⁻¹) w + analyticOrderAt hardyW w :=
        analyticOrderAt_mul hu (hardyW_analyticAt hw)
    _ = analyticOrderAt hardyW w := by rw [hu0, zero_add]

theorem analyticOrderAt_hardyW_conj {w : ℂ} (hw : w.im ≠ 0) :
    analyticOrderAt hardyW (conj w) = analyticOrderAt hardyW w := by
  have hw' : (conj w).im ≠ 0 := by simpa using hw
  have hev : (fun z => conj (hardyW (conj z))) =ᶠ[𝓝 (conj w)] hardyW := by
    filter_upwards [isOpen_im_ne_zero.mem_nhds hw'] with z hz
    have hz' : (conj z).im ≠ 0 := by simpa using hz
    rw [hardyW_conj hz, Complex.conj_conj]
  calc analyticOrderAt hardyW (conj w)
      = analyticOrderAt (fun z => conj (hardyW (conj z))) (conj w) := (analyticOrderAt_congr hev).symm
    _ = analyticOrderAt hardyW w := Zeta23.analyticOrderAt_conj_conj _ _

/-- **m_{1−ρ̄} = m_ρ** for non-real ρ. -/
theorem wMult_reflect {ρ : ℂ} (hρ : ρ.im ≠ 0) : wMult (reflect ρ) = wMult ρ := by
  unfold wMult reflect
  have hc : (conj ρ).im ≠ 0 := by simpa using hρ
  rw [analyticOrderAt_hardyW_one_sub hc, analyticOrderAt_hardyW_conj hρ]

end Hardy
end XiPrime
end Zeta23

end
