/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmE/SeamL.lean — discharging the L(s,χ)-seam obligations of Zeta23.ThmE.LSeam from Mathlib.
Mirror of Zeta23/ZetaReflect.lean + Zeta23/Statement/Seam.lean for a primitive Dirichlet character
χ mod q, q > 1.

Paper [thm:E] proof (ii), verbatim: "the multiset of zeros of L(s,χ) is invariant under ρ ↦ 1−ρ̄
with multiplicities (functional equation χ ↔ χ̄ composed with conj L(conj s, χ) = L(s, χ̄)), all
zeros have 0<β<1, and N_χ(t+1) − N_χ(t) ≪_q log(t+3)".  These are CLASSICAL facts about L(s,χ),
not paper inputs.  χ̄ = χ⁻¹ for ℂ-valued characters (`MulChar.star_eq_inv`).

Contents:
  • `LFunction_conj`  :  L(s̄, χ) = conj L(s, χ⁻¹)  (Schwarz reflection; Dirichlet series on
    Re s > 1 + identity theorem on ℂ — L is ENTIRE for χ ≠ 1, so no pole bookkeeping);
  • `analyticOrderAt_LFunction_conj`  :  conjugation order transport (via the generic
    `Zeta23.analyticOrderAt_conj_conj` of ZetaReflect.lean);
  • `rootNumber_ne_zero`  :  W(χ) ≠ 0, derived from the functional equation + L(2,χ) ≠ 0
    (no Gauss-sum evaluation needed);
  • `analyticOrderAt_LFunction_one_sub`  :  order transport through
    `IsPrimitive.completedLFunction_one_sub` (Γ-factor and prefactor nonvanishing in the strip);
  • `L_reflect_zero`, `L_mult_reflect`, `LSeam.one_le_mult_holds`, `LSeam.finite_window_holds`,
    and the package `LSeam_of : 1 < q → χ.IsPrimitive → LSeam χ`.
-/
import Zeta23.ThmE.Statement
import Zeta23.ZetaReflect
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.MulChar.Lemmas
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

open Complex Set Filter Topology DirichletCharacter
open scoped ComplexConjugate

noncomputable section

namespace Zeta23
namespace ThmE

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-! ### 0. Generalities -/

/-- A primitive character mod q > 1 is nontrivial. -/
lemma ne_one_of_primitive (hq : 1 < q) (hprim : χ.IsPrimitive) : χ ≠ 1 := by
  intro h
  rw [IsPrimitive, h, conductor_one] at hprim
  omega

omit [NeZero q] in
lemma inv_ne_one (hχ1 : χ ≠ 1) : χ⁻¹ ≠ 1 := by
  simpa [inv_eq_one] using hχ1

lemma LFunction_two_ne_zero (hχ1 : χ ≠ 1) : χ.LFunction 2 ≠ 0 :=
  LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) (by norm_num)

lemma LFunction_analyticOnNhd (hχ1 : χ ≠ 1) : AnalyticOnNhd ℂ χ.LFunction univ :=
  (differentiable_LFunction hχ1).differentiableOn.analyticOnNhd isOpen_univ

/-! ### 1. Schwarz reflection:  L(s̄, χ) = conj L(s, χ⁻¹) -/

private lemma LFunction_conj_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    conj ((χ⁻¹).LFunction s) = χ.LFunction (conj s) := by
  have hs' : (1 : ℝ) < (conj s).re := by rwa [Complex.conj_re]
  rw [LFunction_eq_LSeries _ hs, LFunction_eq_LSeries _ hs']
  unfold LSeries
  calc (starRingEnd ℂ) (∑' n, LSeries.term (fun x : ℕ => (χ⁻¹) (x : ZMod q)) s n)
      = ∑' n, star (LSeries.term (fun x : ℕ => (χ⁻¹) (x : ZMod q)) s n) := tsum_star
    _ = ∑' n, LSeries.term (fun x : ℕ => χ (x : ZMod q)) ((starRingEnd ℂ) s) n := by
        congr 1
        funext n
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp [LSeries.term]
        · have harg : ((n : ℂ)).arg ≠ Real.pi := by
            rw [Complex.natCast_arg]
            exact Ne.symm Real.pi_ne_zero
          have hpow : (n : ℂ) ^ (conj s) = conj ((n : ℂ) ^ s) := by
            have h := Complex.cpow_conj (n : ℂ) s harg
            rwa [Complex.conj_natCast] at h
          have hcoef : star ((χ⁻¹) ((n : ℕ) : ZMod q)) = χ ((n : ℕ) : ZMod q) := by
            have h := MulChar.star_apply' χ ((n : ℕ) : ZMod q)
            have h2 := congrArg star h
            rw [star_star] at h2
            exact h2.symm
          simp only [LSeries.term, hn.ne', if_false, star_div₀]
          rw [hcoef]
          simp only [← starRingEnd_apply]
          rw [hpow]

/-- **Schwarz reflection for Dirichlet L**: `L(s̄, χ) = conj L(s, χ⁻¹)` (everywhere; χ ≠ 1). -/
theorem LFunction_conj (hχ1 : χ ≠ 1) (s : ℂ) :
    χ.LFunction (conj s) = conj ((χ⁻¹).LFunction s) := by
  have hL : AnalyticOnNhd ℂ χ.LFunction univ := LFunction_analyticOnNhd hχ1
  have hLt : AnalyticOnNhd ℂ (fun z => conj ((χ⁻¹).LFunction (conj z))) univ := by
    refine DifferentiableOn.analyticOnNhd (fun z _ => ?_) isOpen_univ
    have hd : DifferentiableAt ℂ (χ⁻¹).LFunction (conj z) :=
      (differentiable_LFunction (inv_ne_one hχ1)) _
    have h3 := hd.conj_conj
    rw [Complex.conj_conj] at h3
    exact h3.differentiableWithinAt
  have hagree : χ.LFunction =ᶠ[nhds (2 : ℂ)] (fun z => conj ((χ⁻¹).LFunction (conj z))) := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have h2 : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by norm_num
    filter_upwards [hopen.mem_nhds h2] with z hz
    rw [LFunction_conj_of_one_lt_re (show (1:ℝ) < ((starRingEnd ℂ) z).re by simpa using hz),
      Complex.conj_conj]
  have heq := hL.eqOn_of_preconnected_of_eventuallyEq hLt isPreconnected_univ
    (mem_univ (2 : ℂ)) hagree
  have := heq (mem_univ (conj s))
  simpa using this

/-! ### 2. Order transport under conjugation -/

theorem analyticOrderAt_LFunction_conj (hχ1 : χ ≠ 1) (w : ℂ) :
    analyticOrderAt χ.LFunction (conj w) = analyticOrderAt (χ⁻¹).LFunction w := by
  have hcong : (fun z => conj ((χ⁻¹).LFunction (conj z))) =ᶠ[nhds (conj w)] χ.LFunction := by
    filter_upwards with z
    rw [show z = conj (conj z) from (Complex.conj_conj z).symm, LFunction_conj hχ1 (conj z)]
    simp
  calc analyticOrderAt χ.LFunction (conj w)
      = analyticOrderAt (fun z => conj ((χ⁻¹).LFunction (conj z))) (conj w) :=
        (analyticOrderAt_congr hcong).symm
    _ = analyticOrderAt (χ⁻¹).LFunction w := Zeta23.analyticOrderAt_conj_conj _ _

/-! ### 3. The Γ-factor and the FE prefactor in the strip -/

omit [NeZero q] in
lemma gammaFactor_analyticAt {w : ℂ} (h0 : 0 < w.re) :
    AnalyticAt ℂ (gammaFactor χ) w ∧ gammaFactor χ w ≠ 0 := by
  have key : ∀ a : ℂ, 0 < (w + a).re → AnalyticAt ℂ (fun z => Gammaℝ (z + a)) w ∧
      Gammaℝ (w + a) ≠ 0 := by
    intro a ha
    constructor
    · have hπ : AnalyticAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-(z + a) / 2)) w := by
        rw [analyticAt_iff_eventually_differentiableAt]
        filter_upwards with z
        exact (((differentiableAt_id.add_const a).neg).div_const 2).const_cpow
          (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      have hΓ : AnalyticAt ℂ (fun z : ℂ => Complex.Gamma ((z + a) / 2)) w := by
        rw [analyticAt_iff_eventually_differentiableAt]
        have hopen : IsOpen {z : ℂ | 0 < (z + a).re} := by
          have : Continuous fun z : ℂ => (z + a).re :=
            Complex.continuous_re.comp (continuous_add_const a)
          exact isOpen_lt continuous_const this
        filter_upwards [hopen.mem_nhds ha] with z hz
        have hd : DifferentiableAt ℂ Complex.Gamma ((z + a) / 2) := by
          refine Complex.differentiableAt_Gamma _ fun m => ?_
          intro h
          have h2 : z + a = -2 * (m : ℂ) := by
            rw [div_eq_iff (two_ne_zero (α := ℂ))] at h
            rw [h]; ring
          have h3 : (z + a).re = -2 * (m : ℝ) := by
            rw [h2]
            simp [Complex.mul_re]
          rw [h3] at hz
          have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
          nlinarith
        exact hd.comp z ((differentiableAt_id.add_const a).div_const 2)
      have := hπ.mul hΓ
      refine this.congr ?_
      filter_upwards with z
      simp [Complex.Gammaℝ_def]
    · exact Complex.Gammaℝ_ne_zero_of_re_pos ha
  rcases χ.even_or_odd with he | ho
  · have h := key 0 (by simpa using h0)
    refine ⟨?_, ?_⟩
    · refine h.1.congr ?_
      filter_upwards with z
      simp [he.gammaFactor_def]
    · simpa [he.gammaFactor_def] using h.2
  · have h := key 1 (by simp only [Complex.add_re, Complex.one_re]; linarith)
    refine ⟨?_, ?_⟩
    · refine h.1.congr ?_
      filter_upwards with z
      simp [ho.gammaFactor_def]
    · simpa [ho.gammaFactor_def] using h.2

/-- `Λ = γ·L` on the right half plane (`q > 1`), as an eventual equality near strip points. -/
lemma completed_eq_gamma_mul_L (hq : 1 < q) {w : ℂ} (h0 : 0 < w.re) :
    completedLFunction χ =ᶠ[nhds w] gammaFactor χ * χ.LFunction := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds h0] with z hz
  have hγ : gammaFactor χ z ≠ 0 := by
    rcases χ.even_or_odd with he | ho
    · simpa [he.gammaFactor_def] using Complex.Gammaℝ_ne_zero_of_re_pos hz
    · have h1 : 0 < (z + 1).re := by
        simp only [Complex.add_re, Complex.one_re]
        linarith [hz]
      simpa [ho.gammaFactor_def] using Complex.Gammaℝ_ne_zero_of_re_pos h1
  have hL := LFunction_eq_completed_div_gammaFactor χ z (Or.inr (by omega : q ≠ 1))
  show completedLFunction χ z = gammaFactor χ z * χ.LFunction z
  rw [hL]
  field_simp

/-- **W(χ) ≠ 0** for primitive χ mod q > 1 — derived from the functional equation and
L(2,χ) ≠ 0 (no Gauss-sum input). -/
theorem rootNumber_ne_zero (hq : 1 < q) (hprim : χ.IsPrimitive) : rootNumber χ ≠ 0 := by
  intro hW
  have hχ1 := ne_one_of_primitive hq hprim
  -- FE at s = −1: Λ_χ(2) = q^{−3/2}·W(χ)·Λ_{χ⁻¹}(−1) = 0
  have hFE := hprim.completedLFunction_one_sub (-1 : ℂ)
  rw [hW] at hFE
  simp only [mul_zero, zero_mul] at hFE
  -- so Λ_χ(2) = 0, but Λ_χ(2) = γ(2)·L(2,χ) with L(2,χ) ≠ 0 and γ(2) ≠ 0
  have h2 : completedLFunction χ 2 = 0 := by
    have : (1 : ℂ) - (-1) = 2 := by ring
    rwa [this] at hFE
  have hγL := (completed_eq_gamma_mul_L (χ := χ) hq
    (show (0:ℝ) < (2:ℂ).re by norm_num)).self_of_nhds
  rw [h2, Pi.mul_apply] at hγL
  have hγ := (gammaFactor_analyticAt (χ := χ) (show (0:ℝ) < (2:ℂ).re by norm_num)).2
  have hL2 := LFunction_two_ne_zero hχ1
  rcases mul_eq_zero.mp hγL.symm with h | h
  · exact hγ h
  · exact hL2 h

/-! ### 4. Order transport through the functional equation -/

/-- For `w` in the open strip: `ord_{1−w} L(·,χ) = ord_w L(·,χ⁻¹)`. -/
theorem analyticOrderAt_LFunction_one_sub (hq : 1 < q) (hprim : χ.IsPrimitive)
    {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    analyticOrderAt χ.LFunction (1 - w) = analyticOrderAt (χ⁻¹).LFunction w := by
  have hχ1 := ne_one_of_primitive hq hprim
  have hχ1' := inv_ne_one hχ1
  have h0' : 0 < (1 - w).re := by simp [Complex.sub_re]; linarith
  -- prefactor e(z) = q^{z−1/2}·W(χ): analytic, nonvanishing
  set e : ℂ → ℂ := fun z => (q : ℂ) ^ (z - 1/2) * rootNumber χ with he
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have hean : ∀ z : ℂ, AnalyticAt ℂ e z := by
    intro z
    rw [analyticAt_iff_eventually_differentiableAt]
    filter_upwards with x
    exact ((differentiableAt_id.sub_const _).const_cpow (Or.inl hqC)).mul_const _
  have hene : ∀ z : ℂ, e z ≠ 0 := fun z => mul_ne_zero
    (by rw [Complex.cpow_def_of_ne_zero hqC]; exact Complex.exp_ne_zero _)
    (rootNumber_ne_zero hq hprim)
  -- orders of L and Λ agree in the right half plane
  have hLΛ : ∀ (ψ : DirichletCharacter ℂ q), ψ ≠ 1 → ∀ {z : ℂ}, 0 < z.re →
      analyticOrderAt (completedLFunction ψ) z = analyticOrderAt ψ.LFunction z := by
    intro ψ hψ z hz
    rw [analyticOrderAt_congr (completed_eq_gamma_mul_L (χ := ψ) hq hz)]
    obtain ⟨hγan, hγne⟩ := gammaFactor_analyticAt (χ := ψ) hz
    have hLan : AnalyticAt ℂ ψ.LFunction z := (differentiable_LFunction hψ).analyticAt z
    simp only [analyticOrderAt_mul hγan hLan, hγan.analyticOrderAt_eq_zero.mpr hγne, zero_add]
  -- FE as an eventual identity near w
  have hev : (completedLFunction χ ∘ fun z : ℂ => 1 - z) =ᶠ[nhds w]
      e * completedLFunction χ⁻¹ := by
    filter_upwards with z
    show completedLFunction χ (1 - z) = e z * completedLFunction χ⁻¹ z
    rw [hprim.completedLFunction_one_sub z, he]
  have hg : AnalyticAt ℂ (fun z : ℂ => 1 - z) w := analyticAt_const.sub analyticAt_id
  have hg' : deriv (fun z : ℂ => 1 - z) w ≠ 0 := by
    have : deriv (fun z : ℂ => 1 - z) w = -1 := by
      rw [deriv_const_sub]; simp
    rw [this]; simp
  have hΛan : AnalyticAt ℂ (completedLFunction χ⁻¹) w :=
    (differentiable_completedLFunction hχ1').analyticAt w
  calc analyticOrderAt χ.LFunction (1 - w)
      = analyticOrderAt (completedLFunction χ) (1 - w) := (hLΛ χ hχ1 h0').symm
    _ = analyticOrderAt (completedLFunction χ ∘ fun z : ℂ => 1 - z) w := by
        rw [analyticOrderAt_comp_of_deriv_ne_zero hg hg']
    _ = analyticOrderAt (e * completedLFunction χ⁻¹) w := analyticOrderAt_congr hev
    _ = analyticOrderAt (completedLFunction χ⁻¹) w := by
        simp only [analyticOrderAt_mul (hean w) hΛan,
          (hean w).analyticOrderAt_eq_zero.mpr (hene w), zero_add]
    _ = analyticOrderAt (χ⁻¹).LFunction w := hLΛ χ⁻¹ hχ1' h0

/-! ### 5. The LSeam fields -/

/-- multiplicity invariance under `ρ ↦ 1 − ρ̄`. -/
theorem L_mult_reflect (hq : 1 < q) (hprim : χ.IsPrimitive) :
    ∀ ρ, IsNontrivialZeroL χ ρ → zeroMultL χ (reflect ρ) = zeroMultL χ ρ := by
  rintro ρ ⟨hzero, h0, h1⟩
  have hχ1 := ne_one_of_primitive hq hprim
  have hrefl_eq : reflect ρ = 1 - conj ρ := rfl
  have hc0 : 0 < (conj ρ).re := by rwa [Complex.conj_re]
  have hc1 : (conj ρ).re < 1 := by rwa [Complex.conj_re]
  unfold zeroMultL
  rw [hrefl_eq, analyticOrderAt_LFunction_one_sub hq hprim hc0 hc1,
    analyticOrderAt_LFunction_conj (χ := χ⁻¹) (inv_ne_one hχ1) ρ, inv_inv]

/-- zero-set invariance under `ρ ↦ 1 − ρ̄`. -/
theorem L_reflect_zero (hq : 1 < q) (hprim : χ.IsPrimitive) :
    ∀ ρ, IsNontrivialZeroL χ ρ → IsNontrivialZeroL χ (reflect ρ) := by
  rintro ρ ⟨hzero, h0, h1⟩
  have hχ1 := ne_one_of_primitive hq hprim
  refine ⟨?_, ?_, ?_⟩
  · -- L(1 − ρ̄, χ) = 0
    have hLconj : (χ⁻¹).LFunction (conj ρ) = 0 := by
      have := LFunction_conj (inv_ne_one hχ1) ρ
      rw [inv_inv] at this
      rw [this, hzero, map_zero]
    have hΛ : completedLFunction χ⁻¹ (conj ρ) = 0 := by
      have hγL := (completed_eq_gamma_mul_L (χ := χ⁻¹) hq
        (show 0 < (conj ρ).re by rwa [Complex.conj_re])).self_of_nhds
      rw [hγL, Pi.mul_apply, hLconj, mul_zero]
    have hFE := hprim.completedLFunction_one_sub (conj ρ)
    rw [hΛ, mul_zero] at hFE
    have hre : 0 < (1 - conj ρ).re := by
      simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
      linarith
    have hγL := (completed_eq_gamma_mul_L (χ := χ) hq hre).self_of_nhds
    rw [hFE, Pi.mul_apply] at hγL
    have hγ := (gammaFactor_analyticAt (χ := χ) hre).2
    have hrefl : reflect ρ = 1 - conj ρ := rfl
    rw [hrefl]
    rcases mul_eq_zero.mp hγL.symm with h | h
    · exact absurd h hγ
    · exact h
  · show 0 < (reflect ρ).re
    simp only [Zeta23.reflect, Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  · show (reflect ρ).re < 1
    simp only [Zeta23.reflect, Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith

/-- H-fin for L(s,χ). -/
theorem LSeam_one_le_mult (hq : 1 < q) (hprim : χ.IsPrimitive) :
    ∀ ρ, IsNontrivialZeroL χ ρ → 1 ≤ zeroMultL χ ρ := by
  intro ρ h
  have hχ1 := ne_one_of_primitive hq hprim
  have han : AnalyticAt ℂ χ.LFunction ρ := LFunction_analyticOnNhd hχ1 ρ (mem_univ ρ)
  have hne0 : analyticOrderAt χ.LFunction ρ ≠ 0 := han.analyticOrderAt_ne_zero.mpr h.1
  have hnetop : analyticOrderAt χ.LFunction ρ ≠ ⊤ := by
    refine (LFunction_analyticOnNhd hχ1).analyticOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (mem_univ (2 : ℂ)) (mem_univ ρ) ?_
    rw [(LFunction_analyticOnNhd hχ1 2 (mem_univ _)).analyticOrderAt_eq_zero.mpr
      (LFunction_two_ne_zero hχ1)]
    exact ENat.zero_ne_top
  unfold zeroMultL
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hnetop
  rw [← hn] at hne0 ⊢
  simp only [ENat.toNat_coe, ne_eq, Nat.cast_eq_zero] at hne0 ⊢
  omega

/-- local finiteness of the zeros of L(·,χ) in ordinate windows. -/
theorem LSeam_finite_window (hq : 1 < q) (hprim : χ.IsPrimitive) (T₁ T₂ : ℝ) :
    ({ρ | IsNontrivialZeroL χ ρ} ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂}).Finite := by
  have hχ1 := ne_one_of_primitive hq hprim
  have hloc : ∀ z : ℂ, ∃ t ∈ 𝓝 z, (t ∩ {ρ : ℂ | χ.LFunction ρ = 0}).Finite := by
    intro z
    rcases (LFunction_analyticOnNhd hχ1).eqOn_zero_or_eventually_ne_zero_of_preconnected
      isPreconnected_univ with hzero | hcod
    · exact absurd (hzero (mem_univ (2 : ℂ))) (LFunction_two_ne_zero hχ1)
    · rw [Filter.Eventually, codiscreteWithin_iff_locallyFiniteComplementWithin] at hcod
      obtain ⟨t, ht, hfin⟩ := hcod z (mem_univ z)
      refine ⟨t, ht, hfin.subset ?_⟩
      rintro s ⟨hst, hs0⟩
      exact ⟨hst, mem_univ s, by simpa using hs0⟩
  set K : Set ℂ := (Icc 0 1) ×ℂ (Icc T₁ T₂) with hK
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  choose t ht hfin using hloc
  obtain ⟨I, -, hcover⟩ := hKc.elim_nhds_subcover t (fun z _ => ht z)
  have hfinU : (⋃ z ∈ I, (t z ∩ {ρ : ℂ | χ.LFunction ρ = 0})).Finite :=
    I.finite_toSet.biUnion fun z _ => hfin z
  refine hfinU.subset ?_
  rintro ρ ⟨hρ, hT₁, hT₂⟩
  have hρK : ρ ∈ K := ⟨⟨hρ.2.1.le, hρ.2.2.le⟩, ⟨hT₁.le, hT₂⟩⟩
  obtain ⟨z, hzI, hρz⟩ := mem_iUnion₂.mp (hcover hρK)
  exact mem_iUnion₂.mpr ⟨z, hzI, hρz, hρ.1⟩

/-- **The seam, discharged**: a primitive χ mod q > 1 satisfies all four LSeam obligations. -/
theorem LSeam_of (hq : 1 < q) (hprim : χ.IsPrimitive) : LSeam χ :=
  ⟨LSeam_one_le_mult hq hprim, L_reflect_zero hq hprim, L_mult_reflect hq hprim,
    LSeam_finite_window hq hprim⟩

end ThmE
end Zeta23
