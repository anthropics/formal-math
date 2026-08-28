/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Seam.lean — the seam facts for ξ′.

Discharges `XiDerivSeam` (Zeta23/XiPrime/Statement.lean §2) given (F2):
  theorem xiDerivSeam_of_strip (hF2 : XiDerivZerosInStrip) : XiDerivSeam
((F2) is used ONLY for finite_window, via compactness of [0,1]×[T₁,T₂]; the other three fields are
unconditional theorems below), and exports the classical symmetry/analytic facts about ξ and ξ′ that
ZeroCount/** and ExplicitFormula/** consume:
  §1  ξ = s(s−1)/2 · Γℝ · ζ on Re s > 0 (s ≠ 1); Schwarz reflection ξ(s̄) = conj ξ(s) (all s);
      ξ′(1−s) = −ξ′(s), ξ′(s̄) = conj ξ′(s), and the logDeriv forms (all s, no side conditions: ξ′ entire);
  §2  ξ′ ≢ 0 (finite analytic order everywhere), multiplicity facts, reflection invariance of the order,
      finiteness of zeros in compact sets, the seam;
  §3  h(s) := s(s−1)/2·Γℝ(s), L := h′/h = Γℝ′/Γℝ + 1/s + 1/(s−1) (`Lfn`),
      ξ′ = h′ζ + hζ′ and logDeriv ξ = L + ζ′/ζ on Re s > 0, and Y := ξ′/Γℝ with its closed form
      Y = (s − 1/2)ζ + s(s−1)/2·(Γℝ′/Γℝ·ζ + ζ′)  (the object every zero-count estimate is about:
      analytic on Re s > 0, same zeros and orders as ξ′ there, polynomial growth).
-/
import Zeta23.XiPrime.Statement
import Zeta23.ZetaReflect
import Zeta23.RvM.Fold
import Zeta23.RvM.GammaSide
import Zeta23.RvM.CountByIntegral
import Zeta23.WeilEF.Effective
import Zeta23.Analytic.RectangleLogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Shift

open Complex Set Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Zeta23
namespace XiPrime

/-! ### §1. ξ against Γℝ·ζ; reflection symmetries of ξ and ξ′  [XF′ (F1)] -/

theorem xi_eq_weilXi' : xi = Zeta23.WeilEF.xi := rfl

theorem xi_two : xi 2 = (Real.pi : ℂ) / 6 := Zeta23.WeilEF.xi_two

theorem xi_one : xi 1 = 1 / 2 := by simp [xi]

theorem xi_analyticAt (s : ℂ) : AnalyticAt ℂ xi s :=
  xi_differentiable.analyticAt s

theorem xiDeriv_analyticAt (s : ℂ) : AnalyticAt ℂ xiDeriv s :=
  xiDeriv_differentiable.analyticAt s

theorem xiDeriv_analyticOnNhd (U : Set ℂ) : AnalyticOnNhd ℂ xiDeriv U := fun s _ => xiDeriv_analyticAt s

/-- for Re s > 0, s ≠ 1:  ξ(s) = s(s−1)/2 · (Γℝ(s) · ζ(s)). -/
theorem xi_eq_Gammaℝ_mul_zeta {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    xi s = s * (s - 1) / 2 * (Gammaℝ s * riemannZeta s) := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  rw [xi_eq s hs0 hs1, Zeta23.RvM.completedRiemannZeta_eq_Gammaℝ_mul hs0 (Gammaℝ_ne_zero_of_re_pos hs)]

private lemma conj_ne_one {s : ℂ} (hs : s ≠ 1) : conj s ≠ 1 := fun h => by
  have h2 := congrArg (starRingEnd ℂ) h
  simp only [Complex.conj_conj, map_one] at h2
  exact hs h2

private lemma xi_conj_of_one_lt_re {s : ℂ} (hs : 1 < s.re) : conj (xi (conj s)) = xi s := by
  have hs' : 1 < (conj s).re := by rwa [Complex.conj_re]
  have h1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
  rw [xi_eq_Gammaℝ_mul_zeta (by linarith) (conj_ne_one h1), xi_eq_Gammaℝ_mul_zeta (by linarith) h1,
    Zeta23.RvM.Gammaℝ_conj, _root_.riemannZeta_conj]
  simp only [map_mul, map_sub, map_div₀, map_one, Complex.conj_conj, map_ofNat]

/-- **Schwarz reflection for ξ**: ξ(s̄) = conj ξ(s) for every s (ξ is entire and real on (1,∞)). -/
theorem xi_conj (s : ℂ) : xi (conj s) = conj (xi s) := by
  have hξ : AnalyticOnNhd ℂ xi univ := fun z _ => xi_analyticAt z
  have hξt : AnalyticOnNhd ℂ (fun z => conj (xi (conj z))) univ := by
    refine DifferentiableOn.analyticOnNhd (fun z _ => ?_) isOpen_univ
    have h3 := (xi_differentiable (conj z)).conj_conj
    rw [Complex.conj_conj] at h3
    exact h3.differentiableWithinAt
  have hagree : (fun z => conj (xi (conj z))) =ᶠ[𝓝 (2 : ℂ)] xi := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have h2 : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by simp
    filter_upwards [hopen.mem_nhds h2] with z hz
    exact xi_conj_of_one_lt_re hz
  have heq := hξt.eqOn_of_preconnected_of_eventuallyEq hξ isPreconnected_univ (mem_univ _) hagree
  have h3 : conj (xi (conj (conj s))) = xi (conj s) := heq (mem_univ (conj s))
  rw [Complex.conj_conj] at h3
  exact h3.symm

private lemma deriv_conj_symm {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h : ∀ z, f (conj z) = conj (f z)) (s : ℂ) : deriv f (conj s) = conj (deriv f s) := by
  have hd := ((hf s).hasDerivAt).conj_conj
  have hfun : (fun z => conj (f (conj z))) = f := funext fun z => by rw [h, Complex.conj_conj]
  have hd' : HasDerivAt f (conj (deriv f s)) (conj s) := by
    have := hd
    simp only [Function.comp_def] at this
    rwa [hfun] at this
  exact hd'.deriv

/-- ξ′(s̄) = conj ξ′(s). -/
theorem xiDeriv_conj (s : ℂ) : xiDeriv (conj s) = conj (xiDeriv s) :=
  deriv_conj_symm xi_differentiable xi_conj s

/-- (ξ′)′(s̄) = conj (ξ′)′(s). -/
theorem deriv_xiDeriv_conj (s : ℂ) : deriv xiDeriv (conj s) = conj (deriv xiDeriv s) :=
  deriv_conj_symm xiDeriv_differentiable xiDeriv_conj s

/-- **ξ′(1−s) = −ξ′(s)** (differentiate ξ(1−s) = ξ(s)). -/
theorem xiDeriv_one_sub (s : ℂ) : xiDeriv (1 - s) = -xiDeriv s := by
  unfold xiDeriv
  have h : xi = fun z => xi (1 - z) := funext fun z => (xi_one_sub z).symm
  have h2 : deriv xi s = deriv (fun z => xi (1 - z)) s := congrArg (fun f => deriv f s) h
  rw [h2, deriv_comp_const_sub]
  ring

/-- (ξ′)′(1−s) = (ξ′)′(s). -/
theorem deriv_xiDeriv_one_sub (s : ℂ) : deriv xiDeriv (1 - s) = deriv xiDeriv s := by
  have h : xiDeriv = fun z => -xiDeriv (1 - z) := funext fun z => by rw [xiDeriv_one_sub]; ring
  have h2 : deriv xiDeriv s = deriv (fun z => -xiDeriv (1 - z)) s := congrArg (fun f => deriv f s) h
  rw [h2]
  simp [deriv_comp_const_sub]

/-- logDeriv ξ′ (1−s) = −logDeriv ξ′ (s) — at EVERY s (at a zero both sides are 0). -/
theorem logDeriv_xiDeriv_one_sub (s : ℂ) : logDeriv xiDeriv (1 - s) = -logDeriv xiDeriv s := by
  rw [logDeriv_apply, logDeriv_apply, deriv_xiDeriv_one_sub, xiDeriv_one_sub, div_neg]

/-- logDeriv ξ′ (s̄) = conj (logDeriv ξ′ s) — at every s. -/
theorem logDeriv_xiDeriv_conj (s : ℂ) : logDeriv xiDeriv (conj s) = conj (logDeriv xiDeriv s) := by
  rw [logDeriv_apply, logDeriv_apply, deriv_xiDeriv_conj, xiDeriv_conj, map_div₀]

/-- the fold symmetry: logDeriv ξ′ (1 − s̄) = −conj (logDeriv ξ′ s), every s. -/
theorem logDeriv_xiDeriv_one_sub_conj (s : ℂ) :
    logDeriv xiDeriv (1 - conj s) = -conj (logDeriv xiDeriv s) := by
  rw [logDeriv_xiDeriv_one_sub, logDeriv_xiDeriv_conj]

/-- ξ′(1 − s̄) = −conj ξ′(s)  (Zeta23.reflect ρ = 1 − conj ρ). -/
theorem xiDeriv_reflect (ρ : ℂ) : xiDeriv (reflect ρ) = -conj (xiDeriv ρ) := by
  unfold reflect
  rw [xiDeriv_one_sub, xiDeriv_conj]

theorem xiDeriv_reflect_eq_zero_iff (ρ : ℂ) : xiDeriv (reflect ρ) = 0 ↔ xiDeriv ρ = 0 := by
  rw [xiDeriv_reflect, neg_eq_zero, map_eq_zero]

/-! ### §2. ξ′ ≢ 0; multiplicities; finiteness; the seam  [XF′ (F1), (F3) "locally finite"] -/

/-- ξ′ is not identically zero near any point (else ξ would be constant, but ξ(2) = π/6 ≠ 1/2 = ξ(1)). -/
theorem analyticOrderAt_xiDeriv_ne_top (s : ℂ) : analyticOrderAt xiDeriv s ≠ ⊤ := by
  intro htop
  rw [analyticOrderAt_eq_top] at htop
  have hall : EqOn xiDeriv 0 univ :=
    (xiDeriv_analyticOnNhd univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ s) htop
  have hconst : xi 2 = xi 1 :=
    is_const_of_deriv_eq_zero xi_differentiable (fun z => hall (mem_univ z)) 2 1
  rw [xi_two, xi_one] at hconst
  have hpi : (Real.pi : ℂ) = 3 := by linear_combination 6 * hconst
  have h3 : Real.pi = 3 := by exact_mod_cast hpi
  linarith [Real.pi_gt_three]

theorem exists_xiDeriv_ne_zero : ∃ z : ℂ, xiDeriv z ≠ 0 := by
  by_contra! h
  exact analyticOrderAt_xiDeriv_ne_top 0 (analyticOrderAt_eq_top.mpr (Eventually.of_forall h))

/-- analyticOrderNatAt ξ′ = xiDerivMult (definitional). -/
theorem analyticOrderNatAt_xiDeriv (ρ : ℂ) : analyticOrderNatAt xiDeriv ρ = xiDerivMult ρ := rfl

theorem xiDerivMult_cast (ρ : ℂ) : (xiDerivMult ρ : ℕ∞) = analyticOrderAt xiDeriv ρ := by
  unfold xiDerivMult
  exact ENat.coe_toNat (analyticOrderAt_xiDeriv_ne_top ρ)

/-- 1 ≤ m_{ρ} ↔ ξ′(ρ) = 0. -/
theorem one_le_xiDerivMult_iff (ρ : ℂ) : 1 ≤ xiDerivMult ρ ↔ xiDeriv ρ = 0 := by
  have ha := xiDeriv_analyticAt ρ
  have h0 : xiDerivMult ρ = 0 ↔ xiDeriv ρ ≠ 0 := by
    rw [← ha.analyticOrderAt_eq_zero, ← xiDerivMult_cast]
    norm_cast
  constructor
  · intro h
    by_contra hne
    have := h0.mpr hne
    omega
  · intro h
    by_contra hlt
    exact (h0.mp (by omega)) h

theorem xiDerivMult_eq_zero_iff (ρ : ℂ) : xiDerivMult ρ = 0 ↔ xiDeriv ρ ≠ 0 := by
  rw [← (xiDeriv_analyticAt ρ).analyticOrderAt_eq_zero, ← xiDerivMult_cast]
  norm_cast

/-- the analytic order of ξ′ is invariant under s ↦ 1 − s … -/
theorem analyticOrderAt_xiDeriv_one_sub (w : ℂ) :
    analyticOrderAt xiDeriv (1 - w) = analyticOrderAt xiDeriv w := by
  have hg : AnalyticAt ℂ (fun z : ℂ => 1 - z) w := analyticAt_const.sub analyticAt_id
  have hg' : deriv (fun z : ℂ => 1 - z) w ≠ 0 := by
    rw [deriv_const_sub]
    simp
  have hev : (xiDeriv ∘ fun z : ℂ => 1 - z) = (fun _ : ℂ => (-1 : ℂ)) * xiDeriv := by
    funext z
    simp [xiDeriv_one_sub]
  have hconst : analyticOrderAt (fun _ : ℂ => (-1 : ℂ)) w = 0 :=
    analyticAt_const.analyticOrderAt_eq_zero.mpr (by norm_num)
  calc analyticOrderAt xiDeriv (1 - w)
      = analyticOrderAt (xiDeriv ∘ fun z : ℂ => 1 - z) w := by
        rw [analyticOrderAt_comp_of_deriv_ne_zero hg hg']
    _ = analyticOrderAt ((fun _ : ℂ => (-1 : ℂ)) * xiDeriv) w := by rw [hev]
    _ = analyticOrderAt (fun _ : ℂ => (-1 : ℂ)) w + analyticOrderAt xiDeriv w :=
        analyticOrderAt_mul analyticAt_const (xiDeriv_analyticAt w)
    _ = analyticOrderAt xiDeriv w := by rw [hconst, zero_add]

/-- … and under s ↦ s̄. -/
theorem analyticOrderAt_xiDeriv_conj (w : ℂ) :
    analyticOrderAt xiDeriv (conj w) = analyticOrderAt xiDeriv w := by
  have hcong : (fun z => conj (xiDeriv (conj z))) = xiDeriv :=
    funext fun z => by rw [xiDeriv_conj, Complex.conj_conj]
  calc analyticOrderAt xiDeriv (conj w)
      = analyticOrderAt (fun z => conj (xiDeriv (conj z))) (conj w) := by rw [hcong]
    _ = analyticOrderAt xiDeriv w := Zeta23.analyticOrderAt_conj_conj _ _

/-- m_{1−ρ̄} = m_ρ  [XF′ (F1)]. -/
theorem xiDerivMult_reflect (ρ : ℂ) : xiDerivMult (reflect ρ) = xiDerivMult ρ := by
  unfold xiDerivMult reflect
  rw [analyticOrderAt_xiDeriv_one_sub, analyticOrderAt_xiDeriv_conj]

/-- zeros of ξ′ in a compact set are finite. -/
theorem xiDeriv_zeros_finite_of_isCompact {K : Set ℂ} (hK : IsCompact K) :
    (K ∩ {ρ | IsXiDerivZero ρ}).Finite := by
  obtain ⟨z₀, hz₀⟩ := exists_xiDeriv_ne_zero
  obtain ⟨R, hR⟩ := (hK.isBounded.union (Bornology.isBounded_singleton (x := z₀))).subset_closedBall 0
  have hR0 : 0 ≤ R := by
    have : z₀ ∈ Metric.closedBall (0 : ℂ) R := hR (Or.inr rfl)
    rw [Metric.mem_closedBall] at this
    exact le_trans dist_nonneg this
  set z : ℂ := ((-R : ℝ) : ℂ) + ((-R : ℝ) : ℂ) * I with hz
  set w : ℂ := ((R : ℝ) : ℂ) + ((R : ℝ) : ℂ) * I with hw
  have hsub : Metric.closedBall (0 : ℂ) R ⊆ Rectangle z w := by
    intro s hs
    rw [Metric.mem_closedBall, dist_zero_right] at hs
    have hre := Complex.abs_re_le_norm s
    have him := Complex.abs_im_le_norm s
    rw [abs_le] at hre him
    have hzre : z.re = -R := by simp [hz]
    have hzim : z.im = -R := by simp [hz]
    have hwre : w.re = R := by simp [hw]
    have hwim : w.im = R := by simp [hw]
    simp only [Rectangle, mem_reProdIm, hzre, hzim, hwre, hwim, uIcc_of_le (by linarith : -R ≤ R), mem_Icc]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hfin := Zeta23.Analytic.finite_zeros_rectangle (xiDeriv_analyticOnNhd (Rectangle z w))
    (hsub (hR (Or.inr rfl))) hz₀
  exact hfin.subset (fun s hs => ⟨hsub (hR (Or.inl hs.1)), hs.2⟩)

/-- under (F2) every height window is finite. -/
theorem finite_window_of_strip (hF2 : XiDerivZerosInStrip) (T₁ T₂ : ℝ) :
    ({ρ | IsXiDerivZero ρ} ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂}).Finite := by
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ℂ Icc T₁ T₂) := isCompact_Icc.reProdIm isCompact_Icc
  apply (xiDeriv_zeros_finite_of_isCompact hK).subset
  rintro ρ ⟨hρ, h1, h2⟩
  obtain ⟨ha, hb⟩ := hF2 ρ hρ
  exact ⟨⟨⟨ha.le, hb.le⟩, ⟨h1.le, h2⟩⟩, hρ⟩

/-- **The ξ′ seam**, given (F2) (used only for finite_window). -/
theorem xiDerivSeam_of_strip (hF2 : XiDerivZerosInStrip) : XiDerivSeam where
  one_le_mult := fun ρ h => (one_le_xiDerivMult_iff ρ).mpr h
  reflect_zero := fun ρ h => (xiDeriv_reflect_eq_zero_iff ρ).mpr h
  mult_reflect := fun ρ _ => xiDerivMult_reflect ρ
  finite_window := finite_window_of_strip hF2


/-! ### §3. h, L = h′/h, and Y = ξ′/Γℝ  [XF′ §0, Lemma 2.1]

h(s) := s(s−1)/2 · Γℝ(s) (so ξ = h·ζ on Re s > 0, s ≠ 1), L := h′/h = Γℝ′/Γℝ + 1/s + 1/(s−1)
([XF′]'s L(s) = 1/s + 1/(s−1) − ½log π + ½ψ(s/2), via Zeta23.RvM.logDeriv_Gammaℝ), and
Y(s) := ξ′(s)/Γℝ(s).  Y is the function all the zero-count estimates of this development are about:
it is analytic on Re s > 0 with the SAME zeros and multiplicities as ξ′ there (Γℝ is analytic and
zero-free on Re s > 0), and unlike ξ′ it has only polynomial growth in |Im s| (closed form below), so
Jensen/Landau on discs centred at 2 + it inside Re s > 0 apply to it exactly as they do to ζ in
Zeta23/RvM/LocalCount.lean. -/

/-- L(s) := Γℝ′/Γℝ(s) + 1/s + 1/(s−1)  (= h′/h). -/
def Lfn (s : ℂ) : ℂ := logDeriv Complex.Gammaℝ s + 1 / s + 1 / (s - 1)

/-- Y(s) := ξ′(s) / Γℝ(s). -/
def Yfn (s : ℂ) : ℂ := xiDeriv s / Gammaℝ s

theorem Lfn_eq_digamma {s : ℂ} (hs : 0 < s.re) :
    Lfn s = -(Real.log Real.pi : ℂ) / 2 + (1 / 2 : ℂ) * Complex.digamma (s / 2) + 1 / s + 1 / (s - 1) := by
  rw [Lfn, Zeta23.RvM.logDeriv_Gammaℝ hs]

/-- ξ′ on Re s > 0, s ≠ 1, by differentiating ξ = s(s−1)/2·Γℝ·ζ. -/
theorem xiDeriv_eq_of_re_pos {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    xiDeriv s = ((2 * s - 1) / 2 * Gammaℝ s + s * (s - 1) / 2 * deriv Gammaℝ s) * riemannZeta s
      + s * (s - 1) / 2 * Gammaℝ s * deriv riemannZeta s := by
  have hopen : IsOpen ({z : ℂ | 0 < z.re} ∩ {(1 : ℂ)}ᶜ) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_compl_singleton
  have hev : xi =ᶠ[𝓝 s] fun z => z * (z - 1) / 2 * (Gammaℝ z * riemannZeta z) := by
    filter_upwards [hopen.mem_nhds ⟨hs, hs1⟩] with z hz
    exact xi_eq_Gammaℝ_mul_zeta hz.1 hz.2
  unfold xiDeriv
  rw [hev.deriv_eq]
  have h1 : HasDerivAt (fun z : ℂ => z * (z - 1) / 2) ((2 * s - 1) / 2) s := by
    have := ((hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)).div_const 2
    exact this.congr_deriv (by simp only [id_eq]; ring)
  have h2 : HasDerivAt Gammaℝ (deriv Gammaℝ s) s := (Zeta23.WeilEF.differentiableAt_Gammaℝ hs).hasDerivAt
  have h3 : HasDerivAt riemannZeta (deriv riemannZeta s) s :=
    (differentiableAt_riemannZeta hs1).hasDerivAt
  have h : HasDerivAt (fun z : ℂ => z * (z - 1) / 2 * (Gammaℝ z * riemannZeta z))
      ((2 * s - 1) / 2 * (Gammaℝ s * riemannZeta s)
        + s * (s - 1) / 2 * (deriv Gammaℝ s * riemannZeta s + Gammaℝ s * deriv riemannZeta s)) s :=
    h1.mul (h2.mul h3)
  rw [h.deriv]
  ring

/-- ξ′ = Γℝ · Y on Re s > 0. -/
theorem xiDeriv_eq_Gammaℝ_mul_Yfn {s : ℂ} (hs : 0 < s.re) : xiDeriv s = Gammaℝ s * Yfn s := by
  unfold Yfn
  rw [mul_div_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos hs)]

/-- **closed form of Y** on Re s > 0, s ≠ 1:  Y = (s − ½)ζ + s(s−1)/2 · (Γℝ′/Γℝ · ζ + ζ′). -/
theorem Yfn_eq {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    Yfn s = (s - 1 / 2) * riemannZeta s
      + s * (s - 1) / 2 * (logDeriv Gammaℝ s * riemannZeta s + deriv riemannZeta s) := by
  have hG := Gammaℝ_ne_zero_of_re_pos hs
  unfold Yfn
  rw [xiDeriv_eq_of_re_pos hs hs1, logDeriv_apply]
  field_simp
  ring

theorem Yfn_analyticAt {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ Yfn s :=
  (xiDeriv_analyticAt s).div (Zeta23.WeilEF.analyticAt_Gammaℝ hs) (Gammaℝ_ne_zero_of_re_pos hs)

theorem Yfn_differentiableAt {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Yfn s :=
  (Yfn_analyticAt hs).differentiableAt

theorem Yfn_analyticOnNhd {U : Set ℂ} (hU : U ⊆ {s : ℂ | 0 < s.re}) : AnalyticOnNhd ℂ Yfn U :=
  fun _ hs => Yfn_analyticAt (hU hs)

theorem Yfn_eq_zero_iff {s : ℂ} (hs : 0 < s.re) : Yfn s = 0 ↔ xiDeriv s = 0 := by
  unfold Yfn
  rw [div_eq_zero_iff, or_iff_left (Gammaℝ_ne_zero_of_re_pos hs)]

/-- Y and ξ′ have the same analytic order on Re s > 0. -/
theorem analyticOrderAt_Yfn {s : ℂ} (hs : 0 < s.re) :
    analyticOrderAt Yfn s = analyticOrderAt xiDeriv s := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : xiDeriv =ᶠ[𝓝 s] (Gammaℝ * Yfn) := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact xiDeriv_eq_Gammaℝ_mul_Yfn hz
  have hΓ := Zeta23.WeilEF.analyticAt_Gammaℝ hs
  rw [analyticOrderAt_congr hev, analyticOrderAt_mul hΓ (Yfn_analyticAt hs),
    hΓ.analyticOrderAt_eq_zero.mpr (Gammaℝ_ne_zero_of_re_pos hs), zero_add]

theorem analyticOrderNatAt_Yfn {s : ℂ} (hs : 0 < s.re) : analyticOrderNatAt Yfn s = xiDerivMult s := by
  unfold analyticOrderNatAt xiDerivMult
  rw [analyticOrderAt_Yfn hs]

/-- Y(s̄) = conj Y(s). -/
theorem Yfn_conj (s : ℂ) : Yfn (conj s) = conj (Yfn s) := by
  unfold Yfn
  rw [xiDeriv_conj, Zeta23.RvM.Gammaℝ_conj, map_div₀]

theorem norm_Yfn_conj (s : ℂ) : ‖Yfn (conj s)‖ = ‖Yfn s‖ := by
  rw [Yfn_conj, Complex.norm_conj]

/-- logDeriv ξ′ = Γℝ′/Γℝ + Y′/Y on Re s > 0 wherever ξ′ ≠ 0. -/
theorem logDeriv_xiDeriv_eq {s : ℂ} (hs : 0 < s.re) (hne : xiDeriv s ≠ 0) :
    logDeriv xiDeriv s = logDeriv Gammaℝ s + logDeriv Yfn s := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : xiDeriv =ᶠ[𝓝 s] fun z => Gammaℝ z * Yfn z := by
    filter_upwards [hopen.mem_nhds hs] with z hz
    exact xiDeriv_eq_Gammaℝ_mul_Yfn hz
  have hY : Yfn s ≠ 0 := fun h => hne ((Yfn_eq_zero_iff hs).mp h)
  rw [logDeriv_apply, logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  have hG := Gammaℝ_ne_zero_of_re_pos hs
  have hd : HasDerivAt (fun z : ℂ => Gammaℝ z * Yfn z)
      (deriv Gammaℝ s * Yfn s + Gammaℝ s * deriv Yfn s) s :=
    (Zeta23.WeilEF.differentiableAt_Gammaℝ hs).hasDerivAt.mul (Yfn_differentiableAt hs).hasDerivAt
  rw [hd.deriv]
  field_simp

/-- **logDeriv ξ = L + ζ′/ζ** on Re s > 0, s ≠ 1, ζ(s) ≠ 0  [XF′ Lemma 2.1: ξ′/ξ = L − A]. -/
theorem logDeriv_xi_eq {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (hζ : riemannZeta s ≠ 0) :
    logDeriv xi s = Lfn s + logDeriv riemannZeta s := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hG := Gammaℝ_ne_zero_of_re_pos hs
  rw [logDeriv_apply, show deriv xi s = xiDeriv s from rfl, xiDeriv_eq_of_re_pos hs hs1,
    xi_eq_Gammaℝ_mul_zeta hs hs1, Lfn, logDeriv_apply, logDeriv_apply]
  field_simp
  ring

theorem xi_ne_zero_of_re_pos {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (hζ : riemannZeta s ≠ 0) :
    xi s ≠ 0 := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  rw [xi_eq_Gammaℝ_mul_zeta hs hs1]
  exact mul_ne_zero (div_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) two_ne_zero)
    (mul_ne_zero (Gammaℝ_ne_zero_of_re_pos hs) hζ)

/-- ξ′ = ξ · (L + ζ′/ζ)  (Re s > 0, s ≠ 1, ζ(s) ≠ 0 — in particular on Re s ≥ 1)  [XF′ Lemma 2.1]. -/
theorem xiDeriv_eq_xi_mul {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (hζ : riemannZeta s ≠ 0) :
    xiDeriv s = xi s * (Lfn s + logDeriv riemannZeta s) := by
  rw [← logDeriv_xi_eq hs hs1 hζ, logDeriv_apply, show deriv xi s = xiDeriv s from rfl,
    mul_div_cancel₀ _ (xi_ne_zero_of_re_pos hs hs1 hζ)]

/-- the factorisation used on the line Re s = 2:  Y = s(s−1)/2 · ζ · (L + ζ′/ζ). -/
theorem Yfn_eq_factor {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) (hζ : riemannZeta s ≠ 0) :
    Yfn s = s * (s - 1) / 2 * riemannZeta s * (Lfn s + logDeriv riemannZeta s) := by
  unfold Yfn
  rw [xiDeriv_eq_xi_mul hs hs1 hζ, xi_eq_Gammaℝ_mul_zeta hs hs1]
  have hG := Gammaℝ_ne_zero_of_re_pos hs
  field_simp

/-- in the open strip the zeros of ξ are the zeros of ζ (Statement §1's sanity Prop). -/
theorem xiZerosAreZetaZeros : XiZerosAreZetaZeros := by
  intro s h0 h1
  have hs1 : s ≠ 1 := fun h => by rw [h] at h1; simp at h1
  have hs0 : s ≠ 0 := fun h => by simp [h] at h0
  rw [xi_eq_Gammaℝ_mul_zeta h0 hs1]
  have hA : s * (s - 1) / 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) two_ne_zero
  have hG := Gammaℝ_ne_zero_of_re_pos h0
  constructor
  · intro h
    have h2 := (mul_eq_zero.mp h).resolve_left hA
    exact (mul_eq_zero.mp h2).resolve_left hG
  · intro h
    rw [h, mul_zero, mul_zero]

end XiPrime
end Zeta23
