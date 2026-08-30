/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Hardy/ZFunction.lean — Hardy's Z-function and [XF′ (Z3)]:  Z′(t) = i e^{iϑ(t)} W(½+it)
(branch-free construction).
  G(t) := Γℝ(½+it) (≠ 0),  e(t) := G(t)/‖G(t)‖  (this IS the classical e^{iϑ(t)}: |χ(½+it)| = 1 and
  χ = conj G/G, so e² = 1/χ, e(0) = 1, e(−t) = conj e(t));  ZC(t) := e(t)·ζ(½+it) ∈ ℂ;  hardyZ t := Re ZC(t).
We PROVE: ZC(t) is real (so hardyZ t = ZC t); HasDerivAt ZC (i·e(t)·W(½+it)) t for t ≠ 0 [(Z3)], via
e′/e = i·Re(Γℝ′/Γℝ)(½+it) = i·L₂(½+it); hence the stationary points of Z at height t ≠ 0 are exactly the zeros
of W on the critical line, and Z′(t) = 0 ≠ Z″(t) ⟺ the zero ½+it of W is simple; hence the literal Z′ form of the
W headline (the corollary itself is stated in Final.lean from ncard_simpleStationaryZ).
-/
import Zeta23.XiPrime.Statement
import Zeta23.XiPrime.Hardy.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt

open scoped ComplexConjugate
open Complex Set Filter Topology

noncomputable section

namespace Zeta23
namespace XiPrime

open Hardy

/-- ContinuousSMul ℝ ℂ is not found by instance search in this closure. -/
local instance instContinuousSMulRealComplexZ : ContinuousSMul ℝ ℂ :=
  ⟨((Complex.continuous_ofReal.comp continuous_fst).mul continuous_snd).congr fun p => by
    simp [Complex.real_smul]⟩

/-! ## 1. The phase e(t) = e^{iϑ(t)} and Hardy's Z -/

/-- the critical line parametrisation s(t) = ½ + it. -/
def sline (t : ℝ) : ℂ := 1/2 + t * I

/-- G(t) := Γℝ(½ + it). -/
def Gfun (t : ℝ) : ℂ := Gammaℝ (sline t)

/-- e(t) := G(t)/‖G(t)‖ = e^{iϑ(t)}, ϑ = the Riemann–Siegel theta function (branch-free definition). -/
def ephase (t : ℝ) : ℂ := Gfun t / (‖Gfun t‖ : ℂ)

/-- Hardy's function as a complex number: Z(t) := e^{iϑ(t)} ζ(½+it). -/
def ZC (t : ℝ) : ℂ := ephase t * riemannZeta (sline t)

/-- **Hardy's Z-function** Z : ℝ → ℝ (the real part of ZC; ZC is real, ZC_im below). -/
def hardyZ (t : ℝ) : ℝ := (ZC t).re

@[simp] lemma sline_re (t : ℝ) : (sline t).re = 1/2 := by simp [sline]
@[simp] lemma sline_im (t : ℝ) : (sline t).im = t := by simp [sline]
lemma sline_ne_one (t : ℝ) : sline t ≠ 1 := fun h => by
  have := congrArg Complex.re h; simp at this
lemma conj_sline (t : ℝ) : conj (sline t) = sline (-t) := by
  apply Complex.ext <;> simp [sline]
lemma one_sub_sline (t : ℝ) : 1 - sline t = sline (-t) := by
  apply Complex.ext <;> simp [sline] <;> norm_num

lemma Gfun_ne_zero (t : ℝ) : Gfun t ≠ 0 :=
  Complex.Gammaℝ_ne_zero_of_re_pos (by simp [sline])

lemma normG_pos (t : ℝ) : 0 < ‖Gfun t‖ := norm_pos_iff.mpr (Gfun_ne_zero t)

lemma Gfun_neg (t : ℝ) : Gfun (-t) = conj (Gfun t) := by
  rw [Gfun, Gfun, ← conj_sline, Zeta23.RvM.Gammaℝ_conj]

lemma norm_Gfun_neg (t : ℝ) : ‖Gfun (-t)‖ = ‖Gfun t‖ := by rw [Gfun_neg, Complex.norm_conj]

lemma ephase_ne_zero (t : ℝ) : ephase t ≠ 0 :=
  div_ne_zero (Gfun_ne_zero t) (by exact_mod_cast (normG_pos t).ne')

lemma norm_ephase (t : ℝ) : ‖ephase t‖ = 1 := by
  rw [ephase, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (normG_pos t),
    div_self (normG_pos t).ne']

lemma conj_ephase (t : ℝ) : conj (ephase t) = ephase (-t) := by
  rw [ephase, ephase, map_div₀, Complex.conj_ofReal, Gfun_neg, Complex.norm_conj]

lemma conj_ephase_mul (t : ℝ) : conj (ephase t) * ephase t = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, norm_ephase]; norm_num

/-- χ(½+it) = conj G(t)/G(t). -/
lemma chiFE_sline (t : ℝ) : chiFE (sline t) = conj (Gfun t) / Gfun t := by
  rw [chiFE, one_sub_sline, ← Gfun_neg]; rfl

/-- e(t)² = 1/χ(½+it). -/
lemma ephase_sq (t : ℝ) : ephase t ^ 2 * chiFE (sline t) = 1 := by
  have hG := Gfun_ne_zero t
  have hn : ((‖Gfun t‖ : ℂ)) ≠ 0 := by exact_mod_cast (normG_pos t).ne'
  have hnn : ((‖Gfun t‖ : ℂ)) ^ 2 = conj (Gfun t) * Gfun t := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]; push_cast; ring
  rw [chiFE_sline, ephase, div_pow]
  field_simp
  rw [hnn]; ring

/-- **Z is real**: conj ZC(t) = ZC(t). -/
theorem conj_ZC (t : ℝ) : conj (ZC t) = ZC t := by
  by_cases ht : t = 0
  · subst ht
    rw [ZC, map_mul, conj_ephase, neg_zero, ← Zeta23.riemannZeta_conj (sline_ne_one 0), conj_sline, neg_zero]
  have him : (sline t).im ≠ 0 := by simpa using ht
  rw [ZC, map_mul, ← Zeta23.riemannZeta_conj (sline_ne_one t), conj_sline, ← one_sub_sline]
  -- ζ(1−s) = ζ(s)/χ(s) = ζ(s)·e²
  have hχ := chiFE_ne_zero him
  have h1 : riemannZeta (1 - sline t) = riemannZeta (sline t) * ephase t ^ 2 := by
    have := zeta_eq_chiFE_mul him
    have e2 := ephase_sq t
    calc riemannZeta (1 - sline t) = riemannZeta (sline t) / chiFE (sline t) := by
          rw [this]; field_simp
      _ = riemannZeta (sline t) * ephase t ^ 2 := by
          rw [div_eq_iff hχ, mul_assoc, e2, mul_one]
  rw [h1]
  calc conj (ephase t) * (riemannZeta (sline t) * ephase t ^ 2)
      = (conj (ephase t) * ephase t) * ephase t * riemannZeta (sline t) := by ring
    _ = ephase t * riemannZeta (sline t) := by rw [conj_ephase_mul, one_mul]

theorem ZC_im (t : ℝ) : (ZC t).im = 0 := by
  have := congrArg Complex.im (conj_ZC t)
  simp at this; linarith

theorem hardyZ_eq (t : ℝ) : ((hardyZ t : ℝ) : ℂ) = ZC t := by
  apply Complex.ext <;> simp [hardyZ, ZC_im]

/-! ## 2. Derivatives: e′/e = i·Re(Γℝ′/Γℝ)(½+it) = i·L₂(½+it) -/

lemma hasDerivAt_sline (t : ℝ) : HasDerivAt sline I t := by
  have h1 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 t := by simpa using (hasDerivAt_id t).ofReal_comp
  have h2 := (h1.mul_const I).const_add (1/2 : ℂ)
  rw [one_mul] at h2
  exact h2

lemma hasDerivAt_Gfun (t : ℝ) : HasDerivAt Gfun (deriv Gammaℝ (sline t) * I) t := by
  have hd : DifferentiableAt ℂ Gammaℝ (sline t) :=
    Zeta23.WeilEF.differentiableAt_Gammaℝ (by simp)
  exact hd.hasDerivAt.comp t (hasDerivAt_sline t)

/-- g(t) := (Γℝ′/Γℝ)(½+it). -/
def gG (t : ℝ) : ℂ := logDeriv Gammaℝ (sline t)

lemma hasDerivAt_normG (t : ℝ) :
    HasDerivAt (fun t => ‖Gfun t‖) (-(gG t).im * ‖Gfun t‖) t := by
  -- ‖G‖² has derivative 2⟪G, G′⟫ = 2 Re(conj G · G′·) ; G′ = Γℝ′(s)·i
  have h1 := (hasDerivAt_Gfun t).norm_sq
  have h2 := h1.sqrt (pow_pos (normG_pos t) 2).ne'
  have e1 : (fun y => Real.sqrt (‖Gfun y‖ ^ 2)) = fun y => ‖Gfun y‖ := by
    funext y; rw [Real.sqrt_sq (norm_nonneg _)]
  rw [e1] at h2
  convert h2 using 1
  have hG : Gammaℝ (sline t) ≠ 0 := Gfun_ne_zero t
  have hrel : deriv Gammaℝ (sline t) * conj (Gfun t) = gG t * ((‖Gfun t‖ ^ 2 : ℝ) : ℂ) := by
    rw [gG, logDeriv_apply, Gfun]
    have : ((‖Gammaℝ (sline t)‖ ^ 2 : ℝ) : ℂ) = conj (Gammaℝ (sline t)) * Gammaℝ (sline t) := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      try push_cast
      try ring
    rw [this, div_mul_eq_mul_div, eq_div_iff hG]
    try ring
  rw [Real.sqrt_sq (norm_nonneg _), Complex.inner,
    show deriv Gammaℝ (sline t) * I * conj (Gfun t) = (gG t * ((‖Gfun t‖ ^ 2 : ℝ) : ℂ)) * I by
      rw [← hrel]; ring]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, mul_one, zero_sub, sub_zero]
  have hn := (normG_pos t).ne'
  field_simp
  ring

/-- **e′ = i·Re(g)·e**. -/
theorem hasDerivAt_ephase (t : ℝ) : HasDerivAt ephase (I * ((gG t).re : ℂ) * ephase t) t := by
  have hG := Gfun_ne_zero t
  have hn : ((‖Gfun t‖ : ℂ)) ≠ 0 := by exact_mod_cast (normG_pos t).ne'
  have h1 := hasDerivAt_Gfun t
  have h2 : HasDerivAt (fun t => ((‖Gfun t‖ : ℝ) : ℂ)) (((-(gG t).im * ‖Gfun t‖ : ℝ)) : ℂ) t :=
    (hasDerivAt_normG t).ofReal_comp
  have h3 := h1.div h2 hn
  have e : (Gfun / fun t => ((‖Gfun t‖ : ℝ) : ℂ)) = ephase := rfl
  rw [e] at h3
  refine h3.congr_deriv ?_
  -- algebra: (Γℝ′ i ‖G‖ − G·(−Im g ‖G‖))/‖G‖² = i Re(g) G/‖G‖, using Γℝ′ = g·G and i g + Im g = i Re g
  have hG' : Gammaℝ (sline t) ≠ 0 := Gfun_ne_zero t
  have hd : deriv Gammaℝ (sline t) = gG t * Gfun t := by
    rw [gG, logDeriv_apply, Gfun]; field_simp
  have key : I * gG t + (((gG t).im : ℝ) : ℂ) = I * (((gG t).re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [hd, ephase]
  push_cast
  field_simp
  linear_combination key

/-- L₂(½+it) = Re (Γℝ′/Γℝ)(½+it) ∈ ℝ  [XF′ (Z3)], t ≠ 0. -/
theorem L2_sline (t : ℝ) (ht : t ≠ 0) : L2 (sline t) = ((gG t).re : ℂ) := by
  have him : (sline t).im ≠ 0 := by simpa using ht
  rw [L2_eq him, one_sub_sline, ← conj_sline, Zeta23.RvM.logDeriv_Gammaℝ_conj, gG,
    Complex.add_conj]
  push_cast; ring

lemma hasDerivAt_zeta_sline (t : ℝ) : HasDerivAt (fun t => riemannZeta (sline t)) (deriv riemannZeta (sline t) * I) t :=
  (differentiableAt_riemannZeta (sline_ne_one t)).hasDerivAt.comp t (hasDerivAt_sline t)

/-- **[XF′ (Z3)]  Z′(t) = i e^{iϑ(t)} W(½+it)**, t ≠ 0. -/
theorem hasDerivAt_ZC {t : ℝ} (ht : t ≠ 0) : HasDerivAt ZC (I * ephase t * hardyW (sline t)) t := by
  have h := (hasDerivAt_ephase t).fun_mul (hasDerivAt_zeta_sline t)
  refine h.congr_deriv ?_
  rw [hardyW, L2_sline t ht]; ring

lemma hasDerivAt_hardyW_sline {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun t => hardyW (sline t)) (deriv hardyW (sline t) * I) t := by
  have him : (sline t).im ≠ 0 := by simpa using ht
  exact (hardyW_differentiableAt him).hasDerivAt.comp t (hasDerivAt_sline t)

/-- the derivative of i·e·W(½+it). -/
theorem hasDerivAt_dZC {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun t => I * ephase t * hardyW (sline t))
      (-(ephase t) * (deriv hardyW (sline t) + ((gG t).re : ℂ) * hardyW (sline t))) t := by
  have h := ((hasDerivAt_ephase t).const_mul I).mul (hasDerivAt_hardyW_sline ht)
  refine h.congr_deriv ?_
  ring_nf; rw [Complex.I_sq]; ring

/-! ## 3. Real derivatives of Z and the dictionary with zeros of W -/

/-- a complex-valued function of a real variable with identically zero imaginary part has real derivative. -/
lemma im_deriv_eq_zero {f : ℝ → ℂ} {f' : ℂ} {t : ℝ} (hf : HasDerivAt f f' t)
    (hreal : ∀ᶠ y in 𝓝 t, (f y).im = 0) : f'.im = 0 := by
  have h1 : HasDerivAt (fun y => (f y).im) f'.im t := by
    have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hf
    simpa [Function.comp_def] using this
  have h2 : HasDerivAt (fun y => (f y).im) 0 t := by
    refine (hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [hreal] with y hy; exact hy
  exact h1.unique h2

theorem hasDerivAt_hardyZ {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt hardyZ ((I * ephase t * hardyW (sline t)).re) t :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_ZC ht)

/-- Z′(t) as a complex number is i e W(½+it) (which is therefore real). -/
theorem dZC_im {t : ℝ} (ht : t ≠ 0) : (I * ephase t * hardyW (sline t)).im = 0 :=
  im_deriv_eq_zero (hasDerivAt_ZC ht) (Eventually.of_forall ZC_im)

theorem deriv_hardyZ {t : ℝ} (ht : t ≠ 0) : ((deriv hardyZ t : ℝ) : ℂ) = I * ephase t * hardyW (sline t) := by
  rw [(hasDerivAt_hardyZ ht).deriv]
  apply Complex.ext <;> simp [dZC_im ht]

/-- **Z′(t) = 0 ⟺ W(½+it) = 0** (t ≠ 0). -/
theorem deriv_hardyZ_eq_zero_iff {t : ℝ} (ht : t ≠ 0) : deriv hardyZ t = 0 ↔ hardyW (sline t) = 0 := by
  have hd := deriv_hardyZ ht
  constructor
  · intro h
    have h0 : I * ephase t * hardyW (sline t) = 0 := by rw [← hd, h]; simp
    rcases mul_eq_zero.mp h0 with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 Complex.I_ne_zero
      · exact absurd h2 (ephase_ne_zero t)
    · exact h1
  · intro h
    rw [h, mul_zero] at hd
    exact_mod_cast hd

/-- deriv hardyZ agrees with Re(i e W(½+i·)) near any t ≠ 0. -/
lemma deriv_hardyZ_eventuallyEq {t : ℝ} (ht : t ≠ 0) :
    deriv hardyZ =ᶠ[𝓝 t] fun y => (I * ephase y * hardyW (sline y)).re := by
  filter_upwards [isOpen_ne.mem_nhds ht] with y hy
  exact (hasDerivAt_hardyZ hy).deriv

theorem hasDerivAt_deriv_hardyZ {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (deriv hardyZ) ((-(ephase t) * (deriv hardyW (sline t) + ((gG t).re : ℂ) * hardyW (sline t))).re) t := by
  have h' : HasDerivAt (fun y => (I * ephase y * hardyW (sline y)).re)
      ((-(ephase t) * (deriv hardyW (sline t) + ((gG t).re : ℂ) * hardyW (sline t))).re) t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_dZC ht)
  exact h'.congr_of_eventuallyEq (deriv_hardyZ_eventuallyEq ht)

theorem d2ZC_im {t : ℝ} (ht : t ≠ 0) :
    (-(ephase t) * (deriv hardyW (sline t) + ((gG t).re : ℂ) * hardyW (sline t))).im = 0 := by
  refine im_deriv_eq_zero (hasDerivAt_dZC ht) ?_
  filter_upwards [isOpen_ne.mem_nhds ht] with y hy
  exact dZC_im hy

/-- **at a zero of W on the line: Z″(t) ≠ 0 ⟺ W′(½+it) ≠ 0**. -/
theorem deriv2_hardyZ_ne_zero_iff {t : ℝ} (ht : t ≠ 0) (hW : hardyW (sline t) = 0) :
    deriv (deriv hardyZ) t ≠ 0 ↔ deriv hardyW (sline t) ≠ 0 := by
  have him := d2ZC_im ht
  have hderiv := (hasDerivAt_deriv_hardyZ ht).deriv
  rw [hW, mul_zero, add_zero] at him hderiv
  -- the complex number Y := −e·W′(s) is real and deriv (deriv hardyZ) t = Y.re
  have hval : ((deriv (deriv hardyZ) t : ℝ) : ℂ) = -(ephase t) * deriv hardyW (sline t) := by
    rw [hderiv]
    exact Complex.ext (by simp) (by rw [Complex.ofReal_im]; exact him.symm)
  constructor
  · intro h hd
    apply h
    have := hval; rw [hd, mul_zero] at this
    exact_mod_cast this
  · intro h hd
    apply h
    have := hval; rw [hd] at this
    have h0 : -(ephase t) * deriv hardyW (sline t) = 0 := by rw [← this]; simp
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd (neg_eq_zero.mp h1) (ephase_ne_zero t)
    · exact h1

/-- simple zero of W ⟺ W = 0 and W′ ≠ 0 (W analytic off ℝ). -/
theorem wMult_eq_one_iff {s : ℂ} (hs : s.im ≠ 0) : wMult s = 1 ↔ hardyW s = 0 ∧ deriv hardyW s ≠ 0 := by
  have hA := hardyW_analyticAt hs
  have key := hA.analyticOrderAt_deriv_add_one
  unfold wMult
  constructor
  · intro h
    have hne : analyticOrderAt hardyW s ≠ 0 := by
      intro h0; rw [h0] at h; simp at h
    have h0 : hardyW s = 0 := apply_eq_zero_of_analyticOrderAt_ne_zero hne
    refine ⟨h0, ?_⟩
    have hfin : analyticOrderAt hardyW s = 1 := by
      have hnt : analyticOrderAt hardyW s ≠ ⊤ := by intro ht; rw [ht] at h; simp at h
      lift analyticOrderAt hardyW s to ℕ using hnt with n hn
      simp at h; exact_mod_cast h
    have e : (fun z => hardyW z - hardyW s) = hardyW := by funext z; rw [h0, sub_zero]
    rw [e, hfin] at key
    have hd0 : analyticOrderAt (deriv hardyW) s = 0 := by
      by_contra hne0
      have h1 : (1 : ℕ∞) ≤ analyticOrderAt (deriv hardyW) s := ENat.one_le_iff_ne_zero.mpr hne0
      have h2 : (1 : ℕ∞) + 1 ≤ analyticOrderAt (deriv hardyW) s + 1 := add_le_add h1 le_rfl
      rw [key] at h2
      exact absurd h2 (by decide)
    rw [AnalyticAt.analyticOrderAt_eq_zero hA.deriv] at hd0
    exact hd0
  · rintro ⟨h0, hd⟩
    have e : (fun z => hardyW z - hardyW s) = hardyW := by funext z; rw [h0, sub_zero]
    rw [e] at key
    have hd0 : analyticOrderAt (deriv hardyW) s = 0 := (AnalyticAt.analyticOrderAt_eq_zero hA.deriv).mpr hd
    rw [hd0, zero_add] at key
    rw [← key]; rfl

/-! ## 4. The Z′ form of the headline -/

/-- the stationary points of Z in (T, 2T] with Z″ ≠ 0, as a set of reals. -/
def simpleStationaryZ (T : ℝ) : Set ℝ :=
  {t ∈ Ioc T (2 * T) | deriv hardyZ t = 0 ∧ deriv (deriv hardyZ) t ≠ 0}

/-- **dictionary**: for T > 0, t ↦ ½+it maps simpleStationaryZ T bijectively onto the simple zeros of W on the
critical line with height in (T, 2T]. -/
theorem image_simpleStationaryZ {T : ℝ} (hT : 0 < T) :
    sline '' simpleStationaryZ T = zerosInW T (2 * T) ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | wMult ρ = 1} := by
  ext ρ
  constructor
  · rintro ⟨t, ⟨⟨ht1, ht2⟩, hz, hnz⟩, rfl⟩
    have ht : t ≠ 0 := by intro h; rw [h] at ht1; linarith
    have him : (sline t).im ≠ 0 := by simpa using ht
    have hW := (deriv_hardyZ_eq_zero_iff ht).mp hz
    have hd := (deriv2_hardyZ_ne_zero_iff ht hW).mp hnz
    exact ⟨⟨⟨⟨hW, him⟩, by simpa using ht1, by simpa using ht2⟩, by simp⟩, (wMult_eq_one_iff him).mpr ⟨hW, hd⟩⟩
  · rintro ⟨⟨⟨⟨hW, him⟩, h1, h2⟩, hre⟩, hm⟩
    have hρ : ρ = sline ρ.im := by
      apply Complex.ext <;> simp [sline]; simpa using hre
    have ht : ρ.im ≠ 0 := him
    refine ⟨ρ.im, ⟨⟨h1, h2⟩, ?_, ?_⟩, hρ.symm⟩
    · rw [deriv_hardyZ_eq_zero_iff ht, ← hρ]; exact hW
    · have hW' : hardyW (sline ρ.im) = 0 := by rw [← hρ]; exact hW
      rw [deriv2_hardyZ_ne_zero_iff ht hW', ← hρ]
      exact ((wMult_eq_one_iff him).mp hm).2

theorem sline_injective : Function.Injective sline := by
  intro a b h; have := congrArg Complex.im h; simpa using this

theorem ncard_simpleStationaryZ {T : ℝ} (hT : 0 < T) : (simpleStationaryZ T).ncard = N0simpleW T (2 * T) := by
  rw [N0simpleW, ← image_simpleStationaryZ hT, Set.ncard_image_of_injective _ sline_injective]


end XiPrime
end Zeta23
