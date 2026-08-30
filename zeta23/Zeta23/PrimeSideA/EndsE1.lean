/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — [lem:ends], bound for 𝓔₁ (§5.3).  Statement `calE1_bound` consumed by
Zeta23/PrimeSideA/Ends.lean.

ROUTE.  On I×I: |ν|,|ν'| ≤ B;  |K + K_∞| ≤ 2L² (abs_Kfun_le, abs_Kinf_le);
|K_∞ − K| ≤ (s ρ(τ) + ρ(τ')/s)/2 for every s > 0 (abs_Kinf_sub_Kfun_le), with the choice
s := g(τ')/g(τ), g(τ) := (1 + min(τ−T, 2T−τ))⁻² > 0.  Hence pointwise
  |K²−K_∞²||ν||ν'| ≤ L²B² ( ρ(τ)/g(τ)·g(τ') + g(τ)·ρ(τ')/g(τ') )
and integrating over I×I (product structure):  |𝓔₁| ≤ 2L²B² (∫_I ρ/g)(∫_I g),  ∫_I g ≤ 2.
Pointwise majorant (finite partial sums of the HasSum for ρ, ψ antitone, grid lemma):
  ρ(τ) ≤ W(τ−T) + W(2T−τ) + ψ(τ_d − τ)²,   W(Δ) := ψ(Δ)² + h⁻¹∫_{(Δ,∞)}ψ²,
and 1/g = (1+min(τ−T,2T−τ))² ≤ (1+(τ−T))², (1+(2T−τ))², (1+h+|τ_d−τ|)² respectively, so
  ∫_I ρ/g ≤ 2∫_0^T W(u)(1+u)² du + ∫_ℝ ψ(r)²(2+|r|)² dr ≪ L² + L·l   (split at 1; ψ ≤ L,
  ψ(r) ≤ (c/w)/r², ∫_{(Δ,∞)}ψ² ≤ min(8L, (c/w)²/(3Δ³)), log T ≤ 2l).
Budget: |𝓔₁| ≤ C(c_ϱ)·L²B²(L² + L l) ≤ C·L³B² l (L = λl ≤ l).
-/
import Zeta23.PrimeSideA.EndsCore
import Zeta23.Defs.LeafIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators

namespace Zeta23
namespace PrimeSide

variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}

/-! ### Definitions -/

/-- `W(Δ) := ψ(Δ)² + h⁻¹ ∫_{(Δ,∞)} ψ²`. -/
def Wfun (cϱ : ℝ) (p : Setting) (Δ : ℝ) : ℝ :=
  psiA cϱ p Δ ^ 2 + (p.h)⁻¹ * ∫ r in Set.Ioi Δ, psiA cϱ p r ^ 2

/-- distance to the boundary of `I = [T,2T]` (for τ ∈ I): `min(τ−T, 2T−τ)`. -/
def distB (p : Setting) (τ : ℝ) : ℝ := min (τ - p.T) (2 * p.T - τ)

/-- the weight `g(τ) := (1 + min(τ−T,2T−τ))⁻²` (only used for τ ∈ I, where it is in (0,1]). -/
def gwt (p : Setting) (τ : ℝ) : ℝ := ((1 + distB p τ) ^ 2)⁻¹

/-! ### Leaf integrals -/

/-- (Ig) `∫_I g ≤ 2`. -/
theorem setIntegral_gwt_le (hT : 0 < p.T) : ∫ τ in Icc p.T (2 * p.T), gwt p τ ≤ 2 := by
  
  have := Zeta23.LeafIntegrals.Ig_core p.T hT
  unfold gwt distB
  exact this


theorem W1a (hF : LocalHypsCoreW cϱ p F) :
    ∫ u in (0:ℝ)..1, psiA cϱ p u ^ 2 * (1 + u) ^ 2 ≤ 4 * p.L ^ 2 := by
  have hψ0 := psiA_nonneg_of hF
  have hfi : IntervalIntegrable (fun u => psiA cϱ p u ^ 2 * (1 + u) ^ 2) volume 0 1 :=
    hF.psi_sq_integrable.intervalIntegrable.mul_continuousOn (by fun_prop)
  calc ∫ u in (0:ℝ)..1, psiA cϱ p u ^ 2 * (1 + u) ^ 2
      ≤ ∫ u in (0:ℝ)..1, 4 * p.L ^ 2 := by
        refine intervalIntegral.integral_mono_on zero_le_one hfi intervalIntegrable_const ?_
        intro u hu
        have h1 : psiA cϱ p u ^ 2 ≤ p.L ^ 2 := pow_le_pow_left₀ (hψ0 u) (psiA_le_L u) 2
        have h2 : (1 + u) ^ 2 ≤ 4 := by nlinarith [hu.1, hu.2]
        calc psiA cϱ p u ^ 2 * (1 + u) ^ 2 ≤ p.L ^ 2 * 4 :=
              mul_le_mul h1 h2 (sq_nonneg _) (sq_nonneg _)
          _ = 4 * p.L ^ 2 := by ring
    _ = 4 * p.L ^ 2 := by simp

theorem W1b (hF : LocalHypsCoreW cϱ p F) (hT : 1 ≤ p.T) :
    ∫ u in (1:ℝ)..p.T, psiA cϱ p u ^ 2 * (1 + u) ^ 2 ≤ 4 * (cϱ / p.w) ^ 2 := by
  have hψ0 := psiA_nonneg_of hF
  have hw : 0 < p.w := by linarith [hF.one_le_w]
  have h0 : (0:ℝ) ∉ Set.uIcc (1:ℝ) p.T := Set.notMem_uIcc_of_lt zero_lt_one (by linarith)
  have hfi : IntervalIntegrable (fun u => psiA cϱ p u ^ 2 * (1 + u) ^ 2) volume 1 p.T :=
    hF.psi_sq_integrable.intervalIntegrable.mul_continuousOn (by fun_prop)
  have hgi : IntervalIntegrable (fun u : ℝ => 4 * (cϱ / p.w) ^ 2 * u ^ (-2:ℝ)) volume 1 p.T :=
    (intervalIntegral.intervalIntegrable_rpow (Or.inr h0)).const_mul _
  -- pointwise on [1, T]:  ψ(u)² (1+u)² ≤ (c/(w u²))² (2u)² = 4 (c/w)² u⁻²
  have hpt : ∀ u ∈ Set.Icc (1:ℝ) p.T,
      psiA cϱ p u ^ 2 * (1 + u) ^ 2 ≤ 4 * (cϱ / p.w) ^ 2 * u ^ (-2:ℝ) := by
    intro u hu
    have hu0 : 0 < u := by linarith [hu.1]
    have hq : psiA cϱ p u ≤ cϱ / (p.w * u ^ 2) := psiA_le_div_sq hu0.ne'
    have h1u : (1 + u) ^ 2 ≤ (2 * u) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith [hu.1]) 2
    calc psiA cϱ p u ^ 2 * (1 + u) ^ 2 ≤ (cϱ / (p.w * u ^ 2)) ^ 2 * (2 * u) ^ 2 :=
          mul_le_mul (pow_le_pow_left₀ (hψ0 u) hq 2) h1u (sq_nonneg _) (sq_nonneg _)
      _ = 4 * (cϱ / p.w) ^ 2 * u ^ (-2:ℝ) := by
          rw [Real.rpow_neg hu0.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
          field_simp
          ring
  -- ∫_1^T u⁻² = 1 − 1/T ≤ 1
  have hI : ∫ u in (1:ℝ)..p.T, u ^ (-2:ℝ) ≤ 1 := by
    rw [integral_rpow (Or.inr ⟨by norm_num, h0⟩)]
    norm_num
    rw [Real.rpow_neg_one]
    have : 0 ≤ p.T⁻¹ := inv_nonneg.mpr (by linarith)
    linarith
  calc ∫ u in (1:ℝ)..p.T, psiA cϱ p u ^ 2 * (1 + u) ^ 2
      ≤ ∫ u in (1:ℝ)..p.T, 4 * (cϱ / p.w) ^ 2 * u ^ (-2:ℝ) :=
        intervalIntegral.integral_mono_on hT hfi hgi hpt
    _ = 4 * (cϱ / p.w) ^ 2 * ∫ u in (1:ℝ)..p.T, u ^ (-2:ℝ) := intervalIntegral.integral_const_mul _ _
    _ ≤ 4 * (cϱ / p.w) ^ 2 * 1 := by gcongr
    _ = 4 * (cϱ / p.w) ^ 2 := mul_one _


/-- J(u) := ∫_{(u,∞)} ψ² is antitone in u (ψ² ≥ 0). -/
theorem antitone_setIntegral_psiA_sq_Ioi (hF : LocalHypsCoreW cϱ p F) :
    Antitone (fun u : ℝ => ∫ r in Set.Ioi u, psiA cϱ p r ^ 2) := fun _ _ huv =>
  setIntegral_mono_set hF.psi_sq_integrable.integrableOn
    (Filter.Eventually.of_forall fun _ => sq_nonneg _) (Set.Ioi_subset_Ioi huv).eventuallyLE

/-- (W1c) ∫_0^1 J(u)(1+u)² du ≤ 32L, J(u) := ∫_{(u,∞)}ψ² ≤ 8L. -/
theorem W1c (hF : LocalHypsCoreW cϱ p F) :
    ∫ u in (0:ℝ)..1, (∫ r in Set.Ioi u, psiA cϱ p r ^ 2) * (1 + u) ^ 2 ≤ 32 * p.L := by
  have hJanti := antitone_setIntegral_psiA_sq_Ioi hF
  have hL := hF.L_pos
  have hint : IntervalIntegrable
      (fun u : ℝ => (∫ r in Set.Ioi u, psiA cϱ p r ^ 2) * (1 + u) ^ 2) volume 0 1 :=
    hJanti.intervalIntegrable.mul_continuousOn (by fun_prop)
  calc ∫ u in (0:ℝ)..1, (∫ r in Set.Ioi u, psiA cϱ p r ^ 2) * (1 + u) ^ 2
      ≤ ∫ u in (0:ℝ)..1, (32 * p.L : ℝ) := by
        refine intervalIntegral.integral_mono_on zero_le_one hint intervalIntegrable_const
          fun u hu => ?_
        have h4 : (1 + u) ^ 2 ≤ 4 := by nlinarith [hu.1, hu.2]
        calc (∫ r in Set.Ioi u, psiA cϱ p r ^ 2) * (1 + u) ^ 2 ≤ 8 * p.L * 4 :=
              mul_le_mul (setIntegral_psiA_sq_Ioi_le hF u) h4 (sq_nonneg _) (by linarith)
          _ = 32 * p.L := by ring
    _ = 32 * p.L := by rw [intervalIntegral.integral_const]; simp

/-- (W1d) ∫_1^T J(u)(1+u)² du ≤ (4/3)(c/w)² log T: J(u) ≤ (c/w)²/(3u³) and (1+u)² ≤ 4u² on [1,T]. -/
theorem W1d (hF : LocalHypsCoreW cϱ p F) (hT : 1 ≤ p.T) :
    ∫ u in (1:ℝ)..p.T, (∫ r in Set.Ioi u, psiA cϱ p r ^ 2) * (1 + u) ^ 2
      ≤ 4 / 3 * (cϱ / p.w) ^ 2 * Real.log p.T := by
  have hJanti := antitone_setIntegral_psiA_sq_Ioi hF
  have h0 : (0:ℝ) ∉ Set.uIcc (1:ℝ) p.T := by
    rw [Set.uIcc_of_le hT]; exact fun h => by linarith [h.1]
  have hint : IntervalIntegrable
      (fun u : ℝ => (∫ r in Set.Ioi u, psiA cϱ p r ^ 2) * (1 + u) ^ 2) volume 1 p.T :=
    hJanti.intervalIntegrable.mul_continuousOn (by fun_prop)
  have hint2 : IntervalIntegrable (fun u : ℝ => 4 / 3 * (cϱ / p.w) ^ 2 * u⁻¹) volume 1 p.T := by
    refine ContinuousOn.intervalIntegrable (continuousOn_const.mul (continuousOn_inv₀.mono ?_))
    intro x hx hx0
    exact h0 (hx0 ▸ hx)
  calc ∫ u in (1:ℝ)..p.T, (∫ r in Set.Ioi u, psiA cϱ p r ^ 2) * (1 + u) ^ 2
      ≤ ∫ u in (1:ℝ)..p.T, 4 / 3 * (cϱ / p.w) ^ 2 * u⁻¹ := by
        refine intervalIntegral.integral_mono_on hT hint hint2 fun u hu => ?_
        have hu0 : 0 < u := by linarith [hu.1]
        have hJu := setIntegral_psiA_sq_Ioi_le_div hF hu0
        have h4 : (1 + u) ^ 2 ≤ 4 * u ^ 2 := by nlinarith [hu.1]
        calc (∫ r in Set.Ioi u, psiA cϱ p r ^ 2) * (1 + u) ^ 2
            ≤ (cϱ / p.w) ^ 2 / (3 * u ^ 3) * (4 * u ^ 2) :=
              mul_le_mul hJu h4 (sq_nonneg _) (by positivity)
          _ = 4 / 3 * (cϱ / p.w) ^ 2 * u⁻¹ := by field_simp
    _ = 4 / 3 * (cϱ / p.w) ^ 2 * Real.log p.T := by
        rw [intervalIntegral.integral_const_mul, integral_inv h0, div_one]

/-- (W3) the stray term: `∫_ℝ ψ(r)²(2+|r|)² dr ≤ 18L² + 18(c/w)²`, with integrability. -/
theorem W3 (hF : LocalHypsCoreW cϱ p F) :
    Integrable (fun r => psiA cϱ p r ^ 2 * (2 + |r|) ^ 2) ∧
    ∫ r, psiA cϱ p r ^ 2 * (2 + |r|) ^ 2 ≤ 18 * p.L ^ 2 + 18 * (cϱ / p.w) ^ 2 :=
  
  Zeta23.LeafIntegrals.W3_core (psiA cϱ p) p.L cϱ p.w (by linarith [hF.one_le_w]) psiA_abs
    (psiA_nonneg_of hF) psiA_le_L (fun r hr => psiA_le_div_sq hr) hF.psi_sq_integrable

/-! ### Pointwise facts on I -/

theorem distB_nonneg {τ : ℝ} (hτ : τ ∈ Icc p.T (2 * p.T)) : 0 ≤ distB p τ := by
  unfold distB; rcases hτ with ⟨h1, h2⟩; exact le_min (by linarith) (by linarith)

theorem gwt_pos {τ : ℝ} (hτ : τ ∈ Icc p.T (2 * p.T)) : 0 < gwt p τ := by
  unfold gwt; have := distB_nonneg hτ; positivity

/-- on I the log⁺ term of [eq:Bdef] vanishes: `|ν(τ)| ≤ B`. -/
theorem abs_nuX_le_B_onI (hν : NuBound p B ν) (hT : 0 < p.T) {τ : ℝ} (hτ : τ ∈ Icc p.T (2 * p.T)) :
    |ν τ| ≤ B := by
  have h := hν τ
  have hτ0 : 0 ≤ τ := by linarith [hτ.1]
  have hmax : max (Real.log (|τ| / (4 * p.T))) 0 = 0 := by
    rw [max_eq_right]
    apply Real.log_nonpos (by positivity)
    rw [div_le_one (by positivity), abs_of_nonneg hτ0]
    linarith [hτ.2]
  rw [hmax, add_zero] at h
  exact h

/-- the 𝓔₁ majorant kernel with its ν-weights (on `I×I`):
`L²·(ρ(τ)/g(τ)·g(τ') + g(τ)·ρ(τ')/g(τ'))·|ν(τ)||ν(τ')|`,  g = gwt. -/
def majK1 (p : Setting) (F : LocalFun) (ν : ℝ → ℝ) (q : ℝ × ℝ) : ℝ :=
  p.L ^ 2 * (rho p F q.1 / gwt p q.1 * gwt p q.2 + gwt p q.1 * (rho p F q.2 / gwt p q.2))
    * (|ν q.1| * |ν q.2|)

/-- pointwise: `|K²−K∞²|·|νν'| ≤ majK1` on `I×I` (weighted AM–GM; ν-free kernel). -/
theorem abs_E1integrand_le_majK1 (hF : LocalHypsCoreW cϱ p F) {q : ℝ × ℝ} (hq : q ∈ sqI p) :
    |trG2integrand p F ν q - KinfIntegrand p F ν q| ≤ majK1 p F ν q := by
  obtain ⟨h1, h2⟩ := hq
  have hg1 := gwt_pos (p := p) h1
  have hg2 := gwt_pos (p := p) h2
  have hs : 0 < gwt p q.2 / gwt p q.1 := div_pos hg2 hg1
  have hout := abs_Kinf_sub_Kfun_le hF q.1 q.2 hs
  have hK := abs_Kfun_le hF q.1 q.2
  have hKi := abs_Kinf_le hF q.1 q.2
  have hρ1 := rho_nonneg hF q.1
  have hρ2 := rho_nonneg hF q.2
  -- |K² − K∞²| = |K∞ − K| |K + K∞|
  have hdiff : trG2integrand p F ν q - KinfIntegrand p F ν q
      = -((Kinf p F q.1 q.2 - Kfun p F q.1 q.2) * (Kfun p F q.1 q.2 + Kinf p F q.1 q.2))
        * (ν q.1 * ν q.2) := by
    unfold trG2integrand KinfIntegrand; ring
  rw [hdiff, abs_mul, abs_neg, abs_mul, abs_mul]
  have hsum : |Kfun p F q.1 q.2 + Kinf p F q.1 q.2| ≤ 2 * p.L ^ 2 :=
    le_trans (abs_add_le _ _) (by linarith)
  have hw : (gwt p q.2 / gwt p q.1 * rho p F q.1 + rho p F q.2 / (gwt p q.2 / gwt p q.1)) / 2
      = (rho p F q.1 / gwt p q.1 * gwt p q.2 + gwt p q.1 * (rho p F q.2 / gwt p q.2)) / 2 := by
    field_simp
  rw [hw] at hout
  set Rw := rho p F q.1 / gwt p q.1 * gwt p q.2 + gwt p q.1 * (rho p F q.2 / gwt p q.2) with hRw
  have hRw0 : 0 ≤ Rw := by rw [hRw]; positivity
  calc |Kinf p F q.1 q.2 - Kfun p F q.1 q.2| * |Kfun p F q.1 q.2 + Kinf p F q.1 q.2|
        * (|ν q.1| * |ν q.2|)
      ≤ (Rw / 2) * (2 * p.L ^ 2) * (|ν q.1| * |ν q.2|) := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul hout hsum (abs_nonneg _) (by positivity))
          (by positivity)
    _ = majK1 p F ν q := by simp only [majK1, hRw]; ring

/-- `majK1 ≤ L²B²·(ρ/g·g' + g·ρ'/g')` on `I×I` when `|ν| ≤ B` there. -/
theorem majK1_le (hF : LocalHypsCoreW cϱ p F) (hν : NuBound p B ν) (hT : 0 < p.T)
    {q : ℝ × ℝ} (hq : q ∈ sqI p) :
    majK1 p F ν q ≤ p.L ^ 2 * B ^ 2 *
        (rho p F q.1 / gwt p q.1 * gwt p q.2 + gwt p q.1 * (rho p F q.2 / gwt p q.2)) := by
  obtain ⟨h1, h2⟩ := hq
  have hn1 := abs_nuX_le_B_onI hν hT h1
  have hn2 := abs_nuX_le_B_onI hν hT h2
  have hB : 0 ≤ B := le_trans (abs_nonneg _) hn1
  have hRw0 : 0 ≤ rho p F q.1 / gwt p q.1 * gwt p q.2 + gwt p q.1 * (rho p F q.2 / gwt p q.2) := by
    have := rho_nonneg hF q.1; have := rho_nonneg hF q.2
    have := gwt_pos (p := p) h1; have := gwt_pos (p := p) h2
    positivity
  unfold majK1
  calc p.L ^ 2 * (rho p F q.1 / gwt p q.1 * gwt p q.2 + gwt p q.1 * (rho p F q.2 / gwt p q.2))
        * (|ν q.1| * |ν q.2|)
      ≤ p.L ^ 2 * (rho p F q.1 / gwt p q.1 * gwt p q.2 + gwt p q.1 * (rho p F q.2 / gwt p q.2))
        * (B * B) := by
        apply mul_le_mul_of_nonneg_left (mul_le_mul hn1 hn2 (abs_nonneg _) hB) (by positivity)
    _ = _ := by ring

/-- pointwise bound for the 𝓔₁-integrand on `I×I`. -/
theorem abs_E1integrand_le (hF : LocalHypsCoreW cϱ p F) (hν : NuBound p B ν) (hT : 0 < p.T)
    {q : ℝ × ℝ} (hq : q ∈ sqI p) :
    |trG2integrand p F ν q - KinfIntegrand p F ν q|
      ≤ p.L ^ 2 * B ^ 2 *
        (rho p F q.1 / gwt p q.1 * gwt p q.2 + gwt p q.1 * (rho p F q.2 / gwt p q.2)) :=
  (abs_E1integrand_le_majK1 hF hq).trans (majK1_le hF hν hT hq)

/-! ### The majorant for ρ on I -/

/-- `τ_d = T + d h > 2T − h` (since `d = ⌊T/h⌋`). -/
theorem tau_d_gt (hL : 0 < p.L) (_hT : 0 < p.T) : 2 * p.T - p.h < p.tau p.d := by
  have hh : 0 < p.h := by unfold Setting.h; positivity
  have hd : p.d = ⌊p.T / p.h⌋₊ := Setting.d_eq_floor p hL
  have hlt : p.T / p.h < (p.d : ℝ) + 1 := by rw [hd]; exact Nat.lt_floor_add_one _
  have : p.T < ((p.d : ℝ) + 1) * p.h := by rwa [div_lt_iff₀ hh] at hlt
  rw [Setting.tau]
  push_cast
  nlinarith

/-- generic: a finite sum dominated termwise by a grid function is ≤ the grid sum over a range. -/
theorem sum_le_sum_range_of_injOn {α : Type*} (S : Finset α) (ι : α → ℕ) (hι : Set.InjOn ι S)
    (G : ℕ → ℝ) (hG : ∀ m, 0 ≤ G m) (f : α → ℝ) (hf : ∀ k ∈ S, f k ≤ G (ι k)) :
    ∑ k ∈ S, f k ≤ ∑ m ∈ Finset.range (S.sup ι + 1), G m := by
  calc ∑ k ∈ S, f k ≤ ∑ k ∈ S, G (ι k) := Finset.sum_le_sum hf
    _ = ∑ m ∈ S.image ι, G m := (Finset.sum_image hι).symm
    _ ≤ ∑ m ∈ Finset.range (S.sup ι + 1), G m := by
        apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun m _ _ => hG m)
        intro m hm
        rw [Finset.mem_image] at hm
        obtain ⟨k, hk, rfl⟩ := hm
        rw [Finset.mem_range]
        exact Nat.lt_succ_of_le (Finset.le_sup hk)

/-- `h ≤ 1` (as `L ≥ 8 > 2π`). -/
theorem h_le_one (hF : LocalHypsCoreW cϱ p F) : p.h ≤ 1 := by
  have hL := hF.eight_le_L
  unfold Setting.h
  rw [div_le_one (by linarith)]
  linarith [Real.pi_lt_four]

theorem h_pos (hF : LocalHypsCoreW cϱ p F) : 0 < p.h := by
  unfold Setting.h; have := hF.L_pos; positivity

/-- **Pointwise majorant**: for τ ∈ I,
`ρ(τ) ≤ W(τ−T) + W(2T−τ) + ψ(τ_d − τ)²`. -/
theorem rho_le_majorant (hF : LocalHypsCoreW cϱ p F) (hT : 0 < p.T) {τ : ℝ}
    (hτ : τ ∈ Icc p.T (2 * p.T)) :
    rho p F τ ≤ Wfun cϱ p (τ - p.T) + Wfun cϱ p (2 * p.T - τ) + psiA cϱ p (p.tau p.d - τ) ^ 2 := by
  have hL := hF.L_pos
  have hh := h_pos hF
  have hΔL : 0 ≤ τ - p.T := by linarith [hτ.1]
  have hΔR : 0 ≤ 2 * p.T - τ := by linarith [hτ.2]
  have htd := tau_d_gt hL hT
  have hψ0 := psiA_nonneg_of hF
  have hanti' : AntitoneOn (psiA cϱ p) (Set.Ici 0) :=
    psiA_antitoneOn hL.le (by linarith [hF.four_le_cϱ]) (by linarith [hF.one_le_w])
  refine hasSum_le_of_sum_le (hasSum_rho hF τ) (fun S => ?_)
  -- termwise φ̂² ≤ ψ²
  have hterm : ∀ k : {k : ℤ // k ∉ Finset.Ico (0:ℤ) p.d},
      F.phiHat (τ - p.tau k) ^ 2 ≤ psiA cϱ p (τ - p.tau k) ^ 2 := by
    intro k
    have h := hF.phiHat_le_psi (τ - p.tau k)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  -- split S into k < 0 and k ≥ d
  set Sm := S.filter (fun k => k.1 < 0) with hSm
  set Sp := S.filter (fun k => ¬ k.1 < 0) with hSp
  -- LEFT: k < 0, τ − τ_k = (τ−T) + (−k)h
  have hleft : ∑ k ∈ Sm, psiA cϱ p (τ - p.tau k) ^ 2 ≤ Wfun cϱ p (τ - p.T) := by
    set ι : {k : ℤ // k ∉ Finset.Ico (0:ℤ) p.d} → ℕ := fun k => (-k.1).toNat with hι
    set G : ℕ → ℝ := fun m => psiA cϱ p ((τ - p.T) + m * p.h) ^ 2 with hG
    have hinj : Set.InjOn ι Sm := by
      intro a ha b hb hab
      simp only [hSm, Finset.coe_filter, Set.mem_setOf_eq] at ha hb
      simp only [hι] at hab
      apply Subtype.ext
      have := congrArg (fun n : ℕ => (n : ℤ)) hab
      rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)] at this
      omega
    have hf : ∀ k ∈ Sm, psiA cϱ p (τ - p.tau k) ^ 2 ≤ G (ι k) := by
      intro k hk
      simp only [hSm, Finset.mem_filter] at hk
      have hk0 : k.1 < 0 := hk.2
      have hcast : ((ι k : ℕ) : ℝ) = -(k.1 : ℝ) := by
        simp only [hι]
        have : ((-k.1).toNat : ℤ) = -k.1 := Int.toNat_of_nonneg (by omega)
        exact_mod_cast this
      have : τ - p.tau k = (τ - p.T) + (ι k) * p.h := by
        rw [hcast, Setting.tau]; ring
      simp only [hG]
      rw [← this]
    calc ∑ k ∈ Sm, psiA cϱ p (τ - p.tau k) ^ 2
        ≤ ∑ m ∈ Finset.range (Sm.sup ι + 1), G m :=
          sum_le_sum_range_of_injOn Sm ι hinj G (fun m => sq_nonneg _) _ hf
      _ ≤ Wfun cϱ p (τ - p.T) := by
          rw [hG, Wfun]
          exact sum_psiA_sq_grid_le hF hΔL hh _
  -- RIGHT: k ≥ d.  Split k = d (the stray term) from k ≥ d+1.
  have hright : ∑ k ∈ Sp, psiA cϱ p (τ - p.tau k) ^ 2
      ≤ Wfun cϱ p (2 * p.T - τ) + psiA cϱ p (p.tau p.d - τ) ^ 2 := by
    have hSp_ge : ∀ k ∈ Sp, (p.d : ℤ) ≤ k.1 := by
      intro k hk
      simp only [hSp, Finset.mem_filter, not_lt] at hk
      have hk2 := k.2
      simp only [Finset.mem_Ico, not_and, not_lt] at hk2
      exact hk2 hk.2
    set Sd := Sp.filter (fun k => k.1 = (p.d : ℤ)) with hSd
    set Sq := Sp.filter (fun k => ¬ k.1 = (p.d : ℤ)) with hSq
    -- stray term: at most one element, value ψ(τ − τ_d)² = ψ(τ_d − τ)²
    have hstray : ∑ k ∈ Sd, psiA cϱ p (τ - p.tau k) ^ 2 ≤ psiA cϱ p (p.tau p.d - τ) ^ 2 := by
      have hval : ∀ k ∈ Sd, psiA cϱ p (τ - p.tau k) ^ 2 = psiA cϱ p (p.tau p.d - τ) ^ 2 := by
        intro k hk
        simp only [hSd, Finset.mem_filter] at hk
        have hk2 : (k : ℤ) = ((p.d : ℕ) : ℤ) := hk.2
        rw [hk2, ← psiA_even, neg_sub]
      have hcard : Sd.card ≤ 1 := by
        apply Finset.card_le_one.mpr
        intro a ha b hb
        simp only [hSd, Finset.mem_filter] at ha hb
        exact Subtype.ext (ha.2.trans hb.2.symm)
      rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
      have : (Sd.card : ℝ) ≤ 1 := by exact_mod_cast hcard
      nlinarith [sq_nonneg (psiA cϱ p (p.tau p.d - τ))]
    -- k ≥ d+1: τ_k − τ = (τ_d + h − τ) + j h ≥ (2T−τ) + j h, j = k − d − 1
    have hfar : ∑ k ∈ Sq, psiA cϱ p (τ - p.tau k) ^ 2 ≤ Wfun cϱ p (2 * p.T - τ) := by
      set ι : {k : ℤ // k ∉ Finset.Ico (0:ℤ) p.d} → ℕ := fun k => (k.1 - p.d - 1).toNat with hι
      set G : ℕ → ℝ := fun m => psiA cϱ p ((2 * p.T - τ) + m * p.h) ^ 2 with hG
      have hSq_ge : ∀ k ∈ Sq, (p.d : ℤ) + 1 ≤ k.1 := by
        intro k hk
        simp only [hSq, Finset.mem_filter] at hk
        have := hSp_ge k hk.1
        omega
      have hinj : Set.InjOn ι Sq := by
        intro a ha b hb hab
        have ha' := hSq_ge a ha
        have hb' := hSq_ge b hb
        simp only [hι] at hab
        apply Subtype.ext
        have := congrArg (fun n : ℕ => (n : ℤ)) hab
        rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)] at this
        omega
      have hf : ∀ k ∈ Sq, psiA cϱ p (τ - p.tau k) ^ 2 ≤ G (ι k) := by
        intro k hk
        have hk' := hSq_ge k hk
        have hcast : ((ι k : ℕ) : ℝ) = (k.1 : ℝ) - p.d - 1 := by
          simp only [hι]
          have : ((k.1 - p.d - 1).toNat : ℤ) = k.1 - p.d - 1 := Int.toNat_of_nonneg (by omega)
          exact_mod_cast this
        -- τ_k − τ = (τ_d + h − τ) + (ι k) h
        have hdist : p.tau k - τ = (p.tau p.d + p.h - τ) + (ι k) * p.h := by
          rw [hcast, Setting.tau, Setting.tau]; push_cast; ring
        have hge : (2 * p.T - τ) + (ι k) * p.h ≤ p.tau k - τ := by
          rw [hdist]; have : (0:ℝ) ≤ (ι k) * p.h := by positivity
          linarith
        have hnn : 0 ≤ (2 * p.T - τ) + (ι k) * p.h := by positivity
        rw [hG]
        simp only
        rw [← psiA_abs (τ - p.tau k), abs_sub_comm, abs_of_nonneg (le_trans hnn hge)]
        exact pow_le_pow_left₀ (hψ0 _) (hanti' hnn (le_trans hnn hge) hge) 2
      calc ∑ k ∈ Sq, psiA cϱ p (τ - p.tau k) ^ 2
          ≤ ∑ m ∈ Finset.range (Sq.sup ι + 1), G m :=
            sum_le_sum_range_of_injOn Sq ι hinj G (fun m => sq_nonneg _) _ hf
        _ ≤ Wfun cϱ p (2 * p.T - τ) := by
            rw [hG, Wfun]
            exact sum_psiA_sq_grid_le hF hΔR hh _
    calc ∑ k ∈ Sp, psiA cϱ p (τ - p.tau k) ^ 2
        = ∑ k ∈ Sd, psiA cϱ p (τ - p.tau k) ^ 2 + ∑ k ∈ Sq, psiA cϱ p (τ - p.tau k) ^ 2 :=
          (Finset.sum_filter_add_sum_filter_not Sp (fun k => k.1 = (p.d : ℤ)) _).symm
      _ ≤ _ := by linarith
  calc ∑ k ∈ S, F.phiHat (τ - p.tau k) ^ 2
      ≤ ∑ k ∈ S, psiA cϱ p (τ - p.tau k) ^ 2 := Finset.sum_le_sum fun k _ => hterm k
    _ = ∑ k ∈ Sm, psiA cϱ p (τ - p.tau k) ^ 2 + ∑ k ∈ Sp, psiA cϱ p (τ - p.tau k) ^ 2 :=
        (Finset.sum_filter_add_sum_filter_not S (fun k => k.1 < 0) _).symm
    _ ≤ _ := by linarith

/-! ### The weight integrals -/


/-- `∫_I ρ/g ≤ 2[W1a+W1b+h⁻¹(W1c+W1d)] + W3`-type bound:  `∫_I ρ(τ)(1+min(τ−T,2T−τ))² dτ ≤ RHS`. -/
theorem setIntegral_rho_div_gwt_le (hF : LocalHypsCoreW cϱ p F) (_hν : NuBound p B ν) (hT : 1 ≤ p.T) :
    ∫ τ in Icc p.T (2 * p.T), rho p F τ / gwt p τ
      ≤ 2 * (4 * p.L ^ 2 + 4 * (cϱ / p.w) ^ 2
            + (p.h)⁻¹ * (32 * p.L + 4 / 3 * (cϱ / p.w) ^ 2 * Real.log p.T))
        + (18 * p.L ^ 2 + 18 * (cϱ / p.w) ^ 2) := by
  have hT0 : 0 < p.T := by linarith
  have hL := hF.L_pos
  have hh := h_pos hF
  have hh1 := h_le_one hF
  have htd := tau_d_gt hL hT0
  have hψ0 := psiA_nonneg_of hF
  -- the tail integral J(u) := ∫_{(u,∞)} ψ²
  have hJ_nonneg : ∀ u : ℝ, 0 ≤ ∫ r in Set.Ioi u, psiA cϱ p r ^ 2 := fun u =>
    setIntegral_nonneg measurableSet_Ioi (fun r _ => sq_nonneg _)
  have hJ_le : ∀ u : ℝ, ∫ r in Set.Ioi u, psiA cϱ p r ^ 2 ≤ 8 * p.L := fun u =>
    setIntegral_psiA_sq_Ioi_le hF u
  have hJ_anti : Antitone (fun u : ℝ => ∫ r in Set.Ioi u, psiA cϱ p r ^ 2) := by
    intro u v huv
    exact setIntegral_mono_set hF.psi_sq_integrable.integrableOn
      (ae_of_all _ fun r => sq_nonneg _) (Set.Ioi_subset_Ioi huv).eventuallyLE
  have hJ_meas : Measurable (fun u : ℝ => ∫ r in Set.Ioi u, psiA cϱ p r ^ 2) :=
    hJ_anti.measurable
  have hW_nonneg : ∀ u, 0 ≤ Wfun cϱ p u := fun u =>
    add_nonneg (sq_nonneg _) (mul_nonneg (inv_nonneg.mpr hh.le) (hJ_nonneg u))
  -- local integrability of J, of the W-majorant Φ(u) := W(u)(1+u)², and of its two pieces
  have hJon : ∀ s : Set ℝ, volume s ≠ ⊤ → ∀ (e : ℝ → ℝ), Measurable e →
      IntegrableOn (fun u => ∫ r in Set.Ioi (e u), psiA cϱ p r ^ 2) s := by
    intro s hs e he
    refine Integrable.mono' (g := fun _ => 8 * p.L) (integrableOn_const hs)
      ((hJ_meas.comp he).aestronglyMeasurable) (ae_of_all _ fun u => ?_)
    rw [Real.norm_of_nonneg (hJ_nonneg _)]
    exact hJ_le _
  have hvol : ∀ a b : ℝ, volume (Icc a b) ≠ ⊤ := fun a b => by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hΦon : ∀ a b : ℝ, IntegrableOn (fun u => Wfun cϱ p u * (1 + u) ^ 2) (Icc a b) := by
    intro a b
    have h1 : IntegrableOn (fun u => Wfun cϱ p u) (Icc a b) := by
      simp only [Wfun]
      exact hF.psi_sq_integrable.integrableOn.add
        ((hJon _ (hvol a b) id measurable_id).const_mul _)
    exact h1.mul_continuousOn (by fun_prop : Continuous fun u : ℝ => (1 + u) ^ 2).continuousOn
      isCompact_Icc
  have hP1on : ∀ a b : ℝ, IntegrableOn (fun u => psiA cϱ p u ^ 2 * (1 + u) ^ 2) (Icc a b) :=
    fun a b => hF.psi_sq_integrable.integrableOn.mul_continuousOn
      (by fun_prop : Continuous fun u : ℝ => (1 + u) ^ 2).continuousOn isCompact_Icc
  have hP2on : ∀ a b : ℝ, IntegrableOn
      (fun u => (∫ r in Set.Ioi u, psiA cϱ p r ^ 2) * (1 + u) ^ 2) (Icc a b) :=
    fun a b => (hJon _ (hvol a b) id measurable_id).mul_continuousOn
      (by fun_prop : Continuous fun u : ℝ => (1 + u) ^ 2).continuousOn isCompact_Icc
  have hii : ∀ {f : ℝ → ℝ} {a b : ℝ}, a ≤ b → IntegrableOn f (Icc a b) →
      IntervalIntegrable f volume a b := by
    intro f a b hab h
    exact (h.mono_set (by rw [Set.uIcc_of_le hab])).intervalIntegrable
  -- STEP 1: pointwise majorant on I
  have hpt : ∀ τ ∈ Icc p.T (2 * p.T), rho p F τ / gwt p τ
      ≤ Wfun cϱ p (τ - p.T) * (1 + (τ - p.T)) ^ 2
        + Wfun cϱ p (2 * p.T - τ) * (1 + (2 * p.T - τ)) ^ 2
        + psiA cϱ p (p.tau p.d - τ) ^ 2 * (2 + |p.tau p.d - τ|) ^ 2 := by
    intro τ hτ
    have hm0 := distB_nonneg hτ
    have hmaj := rho_le_majorant hF hT0 hτ
    have e : rho p F τ / gwt p τ = rho p F τ * (1 + distB p τ) ^ 2 := by
      unfold gwt; rw [div_inv_eq_mul]
    rw [e]
    have hmL : distB p τ ≤ τ - p.T := min_le_left _ _
    have hmR : distB p τ ≤ 2 * p.T - τ := min_le_right _ _
    have hmS : 1 + distB p τ ≤ 2 + |p.tau p.d - τ| := by
      have := le_abs_self (p.tau p.d - τ); linarith
    have hW1 := hW_nonneg (τ - p.T)
    have hW2 := hW_nonneg (2 * p.T - τ)
    have hsqL : (1 + distB p τ) ^ 2 ≤ (1 + (τ - p.T)) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hsqR : (1 + distB p τ) ^ 2 ≤ (1 + (2 * p.T - τ)) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hsqS : (1 + distB p τ) ^ 2 ≤ (2 + |p.tau p.d - τ|) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hmS 2
    calc rho p F τ * (1 + distB p τ) ^ 2
        ≤ (Wfun cϱ p (τ - p.T) + Wfun cϱ p (2 * p.T - τ) + psiA cϱ p (p.tau p.d - τ) ^ 2)
            * (1 + distB p τ) ^ 2 := mul_le_mul_of_nonneg_right hmaj (sq_nonneg _)
      _ = Wfun cϱ p (τ - p.T) * (1 + distB p τ) ^ 2
          + Wfun cϱ p (2 * p.T - τ) * (1 + distB p τ) ^ 2
          + psiA cϱ p (p.tau p.d - τ) ^ 2 * (1 + distB p τ) ^ 2 := by ring
      _ ≤ _ := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hsqL hW1)
            (mul_le_mul_of_nonneg_left hsqR hW2))
            (mul_le_mul_of_nonneg_left hsqS (sq_nonneg _))
  -- STEP 2: integrability of the three majorant pieces on I
  set I : Set ℝ := Icc p.T (2 * p.T) with hIdef
  have hIvol : volume I ≠ ⊤ := hvol _ _
  have hA : IntegrableOn (fun τ => Wfun cϱ p (τ - p.T) * (1 + (τ - p.T)) ^ 2) I := by
    have h1 : IntegrableOn (fun τ => Wfun cϱ p (τ - p.T)) I := by
      simp only [Wfun]
      exact (hF.psi_sq_integrable.comp_sub_right p.T).integrableOn.add
        ((hJon _ hIvol (fun τ => τ - p.T) (measurable_id.sub_const _)).const_mul _)
    exact h1.mul_continuousOn
      (by fun_prop : Continuous fun τ : ℝ => (1 + (τ - p.T)) ^ 2).continuousOn isCompact_Icc
  have hB : IntegrableOn (fun τ => Wfun cϱ p (2 * p.T - τ) * (1 + (2 * p.T - τ)) ^ 2) I := by
    have h1 : IntegrableOn (fun τ => Wfun cϱ p (2 * p.T - τ)) I := by
      simp only [Wfun]
      exact (hF.psi_sq_integrable.comp_sub_left (2 * p.T)).integrableOn.add
        ((hJon _ hIvol (fun τ => 2 * p.T - τ) (measurable_const.sub measurable_id)).const_mul _)
    exact h1.mul_continuousOn
      (by fun_prop : Continuous fun τ : ℝ => (1 + (2 * p.T - τ)) ^ 2).continuousOn
      isCompact_Icc
  have hC : IntegrableOn
      (fun τ => psiA cϱ p (p.tau p.d - τ) ^ 2 * (2 + |p.tau p.d - τ|) ^ 2) I :=
    ((W3 hF).1.comp_sub_left (p.tau p.d)).integrableOn
  -- STEP 3: integrate the pointwise bound
  have hmono : ∫ τ in I, rho p F τ / gwt p τ
      ≤ ∫ τ in I, (Wfun cϱ p (τ - p.T) * (1 + (τ - p.T)) ^ 2
        + Wfun cϱ p (2 * p.T - τ) * (1 + (2 * p.T - τ)) ^ 2
        + psiA cϱ p (p.tau p.d - τ) ^ 2 * (2 + |p.tau p.d - τ|) ^ 2) := by
    refine integral_mono_of_nonneg ?_ ((hA.add hB).add hC) ?_
    · exact ae_restrict_of_forall_mem measurableSet_Icc fun τ hτ =>
        div_nonneg (rho_nonneg hF τ) (gwt_pos hτ).le
    · exact ae_restrict_of_forall_mem measurableSet_Icc hpt
  -- STEP 4: the three integrals
  -- (C) the stray term
  have hCval : ∫ τ in I, psiA cϱ p (p.tau p.d - τ) ^ 2 * (2 + |p.tau p.d - τ|) ^ 2
      ≤ 18 * p.L ^ 2 + 18 * (cϱ / p.w) ^ 2 := by
    calc ∫ τ in I, psiA cϱ p (p.tau p.d - τ) ^ 2 * (2 + |p.tau p.d - τ|) ^ 2
        ≤ ∫ τ, psiA cϱ p (p.tau p.d - τ) ^ 2 * (2 + |p.tau p.d - τ|) ^ 2 :=
          setIntegral_le_integral ((W3 hF).1.comp_sub_left (p.tau p.d))
            (ae_of_all _ fun τ => by positivity)
      _ = ∫ r, psiA cϱ p r ^ 2 * (2 + |r|) ^ 2 :=
          integral_sub_left_eq_self (fun r => psiA cϱ p r ^ 2 * (2 + |r|) ^ 2) volume (p.tau p.d)
      _ ≤ _ := (W3 hF).2
  -- (A),(B): change of variables to ∫_0^T W(u)(1+u)²
  have hT2 : p.T ≤ 2 * p.T := by linarith
  have hAval : ∫ τ in I, Wfun cϱ p (τ - p.T) * (1 + (τ - p.T)) ^ 2
      = ∫ u in (0:ℝ)..p.T, Wfun cϱ p u * (1 + u) ^ 2 := by
    rw [hIdef, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT2,
      intervalIntegral.integral_comp_sub_right (fun u => Wfun cϱ p u * (1 + u) ^ 2) p.T,
      sub_self, show 2 * p.T - p.T = p.T by ring]
  have hBval : ∫ τ in I, Wfun cϱ p (2 * p.T - τ) * (1 + (2 * p.T - τ)) ^ 2
      = ∫ u in (0:ℝ)..p.T, Wfun cϱ p u * (1 + u) ^ 2 := by
    rw [hIdef, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT2,
      intervalIntegral.integral_comp_sub_left (fun u => Wfun cϱ p u * (1 + u) ^ 2) (2 * p.T),
      sub_self, show 2 * p.T - p.T = p.T by ring]
  -- the main 1-D integral: split at 1 and expand W = ψ² + h⁻¹ J
  have hΦ01 := hii zero_le_one (hΦon 0 1)
  have hΦ1T := hii hT (hΦon 1 p.T)
  have hexpand : ∀ {a b : ℝ}, a ≤ b →
      ∫ u in a..b, Wfun cϱ p u * (1 + u) ^ 2
        = (∫ u in a..b, psiA cϱ p u ^ 2 * (1 + u) ^ 2)
          + (p.h)⁻¹ * ∫ u in a..b, (∫ r in Set.Ioi u, psiA cϱ p r ^ 2) * (1 + u) ^ 2 := by
    intro a b hab
    have e : (fun u => Wfun cϱ p u * (1 + u) ^ 2)
        = fun u => psiA cϱ p u ^ 2 * (1 + u) ^ 2
          + (p.h)⁻¹ * ((∫ r in Set.Ioi u, psiA cϱ p r ^ 2) * (1 + u) ^ 2) := by
      funext u; simp only [Wfun]; ring
    rw [e, intervalIntegral.integral_add (hii hab (hP1on a b))
      ((hii hab (hP2on a b)).const_mul _), intervalIntegral.integral_const_mul]
  have hmain : ∫ u in (0:ℝ)..p.T, Wfun cϱ p u * (1 + u) ^ 2
      ≤ 4 * p.L ^ 2 + 4 * (cϱ / p.w) ^ 2
        + (p.h)⁻¹ * (32 * p.L + 4 / 3 * (cϱ / p.w) ^ 2 * Real.log p.T) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hΦ01 hΦ1T,
      hexpand zero_le_one, hexpand hT]
    have h1 := W1a hF
    have h2 := W1b hF hT
    have h3 := W1c hF
    have h4 := W1d hF hT
    have hhi : 0 ≤ (p.h)⁻¹ := inv_nonneg.mpr hh.le
    nlinarith [mul_le_mul_of_nonneg_left h3 hhi, mul_le_mul_of_nonneg_left h4 hhi]
  -- assemble
  calc ∫ τ in I, rho p F τ / gwt p τ
      ≤ ∫ τ in I, (Wfun cϱ p (τ - p.T) * (1 + (τ - p.T)) ^ 2
          + Wfun cϱ p (2 * p.T - τ) * (1 + (2 * p.T - τ)) ^ 2
          + psiA cϱ p (p.tau p.d - τ) ^ 2 * (2 + |p.tau p.d - τ|) ^ 2) := hmono
    _ = (∫ τ in I, (Wfun cϱ p (τ - p.T) * (1 + (τ - p.T)) ^ 2
          + Wfun cϱ p (2 * p.T - τ) * (1 + (2 * p.T - τ)) ^ 2))
        + ∫ τ in I, psiA cϱ p (p.tau p.d - τ) ^ 2 * (2 + |p.tau p.d - τ|) ^ 2 :=
          integral_add (hA.add hB) hC
    _ = (∫ τ in I, Wfun cϱ p (τ - p.T) * (1 + (τ - p.T)) ^ 2)
        + (∫ τ in I, Wfun cϱ p (2 * p.T - τ) * (1 + (2 * p.T - τ)) ^ 2)
        + ∫ τ in I, psiA cϱ p (p.tau p.d - τ) ^ 2 * (2 + |p.tau p.d - τ|) ^ 2 := by
          rw [integral_add hA hB]
    _ ≤ _ := by rw [hAval, hBval]; linarith [hmain, hCval]

/-! ### Assembly -/

section Bounds
variable (cϱ lam : ℝ)

/-- **Majorant bound behind 𝓔₁**: ∬_{I×I} majK1(ν) ≤ C·L³B²·l for T ≥ T₀. -/
theorem calE1_maj_bound :
    ∃ C T₀ : ℝ, ∀ (p : Setting) (F : LocalFun) (B : ℝ) (ν : ℝ → ℝ), p.lam = lam → T₀ ≤ p.T →
      LocalHypsCoreW cϱ p F → p.L ≤ 2 * p.l → Continuous ν → NuBound p B ν →
      ∫ q in sqI p, majK1 p F ν q ≤ C * (p.L ^ 3 * B ^ 2 * p.l) := by
  refine ⟨4 * (180 + 40 * cϱ ^ 2), (2 * π) ^ 2, fun p F B ν hplam hT hF hL2l hνc hν => ?_⟩
  -- regime
  have hπ := Real.pi_gt_three
  have hT1 : (1:ℝ) ≤ p.T := by nlinarith
  have hT0 : (0:ℝ) < p.T := by linarith
  have hL8 := hF.eight_le_L
  have hL0 := hF.L_pos
  have hc4 := hF.four_le_cϱ
  have hw1 := hF.one_le_w
  have hl1 : (1:ℝ) ≤ p.l := hF.one_le_l
  have hlogT : Real.log p.T ≤ 2 * p.l := by
    -- log T = l + log(2π) and log(2π) ≤ l since T ≥ (2π)²
    have e : Real.log p.T = p.l + Real.log (2 * π) := by
      show Real.log p.T = Real.log (p.T / (2 * π)) + Real.log (2 * π)
      rw [Real.log_div (by linarith) (by positivity)]; ring
    have h2 : Real.log (2 * π) ≤ p.l := by
      show Real.log (2 * π) ≤ Real.log (p.T / (2 * π))
      apply Real.log_le_log (by positivity)
      rw [le_div_iff₀ (by positivity)]; nlinarith
    linarith
  have hB0 : 0 ≤ B := by
    have := abs_nuX_le_B_onI hν hT0 (τ := p.T) ⟨le_rfl, by linarith⟩
    exact le_trans (abs_nonneg _) this
  -- the two 1-D integrals
  have hIg := setIntegral_gwt_le (p := p) hT0
  have hR := setIntegral_rho_div_gwt_le hF hν hT1
  set R := ∫ τ in Icc p.T (2 * p.T), rho p F τ / gwt p τ with hRdef
  set G := ∫ τ in Icc p.T (2 * p.T), gwt p τ with hGdef
  have hG0 : 0 ≤ G := setIntegral_nonneg measurableSet_Icc fun τ hτ => (gwt_pos hτ).le
  have hR0 : 0 ≤ R := setIntegral_nonneg measurableSet_Icc fun τ hτ =>
    div_nonneg (rho_nonneg hF τ) (gwt_pos hτ).le
  -- continuity / integrability on the compact square
  have hρc : Continuous (rho p F) := by
    have := hF.phiHat_cont; unfold rho; fun_prop
  have hdistc : Continuous (distB p) := by unfold distB; fun_prop
  have hgc : ContinuousOn (gwt p) (Icc p.T (2 * p.T)) := by
    unfold gwt
    refine ContinuousOn.inv₀ (by fun_prop) fun τ hτ => ?_
    have := distB_nonneg (p := p) hτ; positivity
  have hρg : ContinuousOn (fun τ => rho p F τ / gwt p τ) (Icc p.T (2 * p.T)) :=
    hρc.continuousOn.div hgc fun τ hτ => (gwt_pos hτ).ne'
  have hfst : ∀ {f : ℝ → ℝ}, ContinuousOn f (Icc p.T (2 * p.T)) →
      ContinuousOn (fun q : ℝ × ℝ => f q.1) (sqI p) := fun hf =>
    hf.comp continuous_fst.continuousOn fun q hq => hq.1
  have hsnd : ∀ {f : ℝ → ℝ}, ContinuousOn f (Icc p.T (2 * p.T)) →
      ContinuousOn (fun q : ℝ × ℝ => f q.2) (sqI p) := fun hf =>
    hf.comp continuous_snd.continuousOn fun q hq => hq.2
  have hM1c : ContinuousOn (fun q : ℝ × ℝ => rho p F q.1 / gwt p q.1 * gwt p q.2) (sqI p) :=
    (hfst hρg).mul (hsnd hgc)
  have hM2c : ContinuousOn (fun q : ℝ × ℝ => gwt p q.1 * (rho p F q.2 / gwt p q.2)) (sqI p) :=
    (hfst hgc).mul (hsnd hρg)
  have hcpt : IsCompact (sqI p) := isCompact_sqI
  have hM1i : IntegrableOn (fun q : ℝ × ℝ => rho p F q.1 / gwt p q.1 * gwt p q.2) (sqI p) :=
    hM1c.integrableOn_compact hcpt
  have hM2i : IntegrableOn (fun q : ℝ × ℝ => gwt p q.1 * (rho p F q.2 / gwt p q.2)) (sqI p) :=
    hM2c.integrableOn_compact hcpt
  have hfi : IntegrableOn (majK1 p F ν) (sqI p) := by
    have hνa : ContinuousOn (fun τ => |ν τ|) (Icc p.T (2 * p.T)) := hνc.abs.continuousOn
    have hc : ContinuousOn (majK1 p F ν) (sqI p) := by
      have := ((hM1c.add hM2c).const_smul (p.L ^ 2)).mul ((hfst hνa).mul (hsnd hνa))
      refine this.congr fun q hq => ?_
      simp only [majK1, Pi.smul_apply, Pi.add_apply, Pi.mul_apply, smul_eq_mul]
    exact hc.integrableOn_compact hcpt
  -- ∫_{sqI} majK1 ≤ L²B²(RG + GR)
  have hmain : ∫ q in sqI p, majK1 p F ν q ≤ p.L ^ 2 * B ^ 2 * (R * G + G * R) := by
    have step2 : ∫ q in sqI p, majK1 p F ν q
        ≤ ∫ q in sqI p, p.L ^ 2 * B ^ 2 *
          (rho p F q.1 / gwt p q.1 * gwt p q.2 + gwt p q.1 * (rho p F q.2 / gwt p q.2)) := by
      refine setIntegral_mono_on hfi ((hM1i.add hM2i).const_mul _) measurableSet_sqI
        fun q hq => majK1_le hF hν hT0 hq
    have step3 : ∫ q in sqI p, p.L ^ 2 * B ^ 2 *
          (rho p F q.1 / gwt p q.1 * gwt p q.2 + gwt p q.1 * (rho p F q.2 / gwt p q.2))
        = p.L ^ 2 * B ^ 2 * (R * G + G * R) := by
      rw [integral_const_mul, integral_add hM1i hM2i]
      congr 1
      unfold sqI
      rw [Measure.volume_eq_prod, setIntegral_prod_mul (fun τ => rho p F τ / gwt p τ) (gwt p),
        setIntegral_prod_mul (gwt p) (fun τ => rho p F τ / gwt p τ)]
      rfl
    linarith
  -- numerics
  have hcw : (cϱ / p.w) ^ 2 ≤ cϱ ^ 2 := by
    have : cϱ / p.w ≤ cϱ := div_le_self (by linarith) hw1
    have : 0 ≤ cϱ / p.w := by positivity
    nlinarith
  have hh : (p.h)⁻¹ = p.L / (2 * π) := by unfold Setting.h; rw [inv_div]
  have hhL : (p.h)⁻¹ ≤ p.L := by
    rw [hh, div_le_iff₀ (by positivity)]; nlinarith
  have hRle : R ≤ (180 + 40 * cϱ ^ 2) * (p.L * p.l) := by
    have hlog0 : 0 ≤ Real.log p.T := Real.log_nonneg hT1
    have h1 : (p.h)⁻¹ * (32 * p.L + 4 / 3 * (cϱ / p.w) ^ 2 * Real.log p.T)
        ≤ p.L * (32 * p.L + 4 / 3 * cϱ ^ 2 * (2 * p.l)) := by
      apply mul_le_mul hhL _ (by positivity) hL0.le
      gcongr
    have hLl2 : p.L ^ 2 ≤ 2 * (p.L * p.l) := by nlinarith
    have hLl1 : 1 ≤ p.L * p.l := by nlinarith
    have hc2 : cϱ ^ 2 ≤ cϱ ^ 2 * (p.L * p.l) := by nlinarith [sq_nonneg cϱ]
    nlinarith
  calc ∫ q in sqI p, majK1 p F ν q ≤ p.L ^ 2 * B ^ 2 * (R * G + G * R) := hmain
    _ = 2 * (p.L ^ 2 * B ^ 2) * (R * G) := by ring
    _ ≤ 2 * (p.L ^ 2 * B ^ 2) * ((180 + 40 * cϱ ^ 2) * (p.L * p.l) * 2) := by
        gcongr
    _ = 4 * (180 + 40 * cϱ ^ 2) * (p.L ^ 3 * B ^ 2 * p.l) := by ring


/-- **Majorant bound behind 𝓔₁, L-intrinsic form** (no bandwidth cap):
∬_{I×I} majK1(ν) ≤ C·L³B²·(L + l) for T ≥ T₀ (l = log(T/2π) carries the genuine log T). -/
theorem calE1_maj_bound_L :
    ∃ C T₀ : ℝ, ∀ (p : Setting) (F : LocalFun) (B : ℝ) (ν : ℝ → ℝ), T₀ ≤ p.T →
      LocalHypsCoreW cϱ p F → Continuous ν → NuBound p B ν →
      ∫ q in sqI p, majK1 p F ν q ≤ C * (p.L ^ 3 * B ^ 2 * (p.L + p.l)) := by
  refine ⟨4 * (90 + 32 * cϱ ^ 2), (2 * π) ^ 2, fun p F B ν hT hF hνc hν => ?_⟩
  -- regime
  have hπ := Real.pi_gt_three
  have hT1 : (1:ℝ) ≤ p.T := by nlinarith
  have hT0 : (0:ℝ) < p.T := by linarith
  have hL8 := hF.eight_le_L
  have hL0 := hF.L_pos
  have hc4 := hF.four_le_cϱ
  have hw1 := hF.one_le_w
  have hl1 : (1:ℝ) ≤ p.l := hF.one_le_l
  have hlogT : Real.log p.T ≤ 2 * p.l := by
    -- log T = l + log(2π) and log(2π) ≤ l since T ≥ (2π)²
    have e : Real.log p.T = p.l + Real.log (2 * π) := by
      show Real.log p.T = Real.log (p.T / (2 * π)) + Real.log (2 * π)
      rw [Real.log_div (by linarith) (by positivity)]; ring
    have h2 : Real.log (2 * π) ≤ p.l := by
      show Real.log (2 * π) ≤ Real.log (p.T / (2 * π))
      apply Real.log_le_log (by positivity)
      rw [le_div_iff₀ (by positivity)]; nlinarith
    linarith
  have hB0 : 0 ≤ B := by
    have := abs_nuX_le_B_onI hν hT0 (τ := p.T) ⟨le_rfl, by linarith⟩
    exact le_trans (abs_nonneg _) this
  -- the two 1-D integrals
  have hIg := setIntegral_gwt_le (p := p) hT0
  have hR := setIntegral_rho_div_gwt_le hF hν hT1
  set R := ∫ τ in Icc p.T (2 * p.T), rho p F τ / gwt p τ with hRdef
  set G := ∫ τ in Icc p.T (2 * p.T), gwt p τ with hGdef
  have hG0 : 0 ≤ G := setIntegral_nonneg measurableSet_Icc fun τ hτ => (gwt_pos hτ).le
  have hR0 : 0 ≤ R := setIntegral_nonneg measurableSet_Icc fun τ hτ =>
    div_nonneg (rho_nonneg hF τ) (gwt_pos hτ).le
  -- continuity / integrability on the compact square
  have hρc : Continuous (rho p F) := by
    have := hF.phiHat_cont; unfold rho; fun_prop
  have hdistc : Continuous (distB p) := by unfold distB; fun_prop
  have hgc : ContinuousOn (gwt p) (Icc p.T (2 * p.T)) := by
    unfold gwt
    refine ContinuousOn.inv₀ (by fun_prop) fun τ hτ => ?_
    have := distB_nonneg (p := p) hτ; positivity
  have hρg : ContinuousOn (fun τ => rho p F τ / gwt p τ) (Icc p.T (2 * p.T)) :=
    hρc.continuousOn.div hgc fun τ hτ => (gwt_pos hτ).ne'
  have hfst : ∀ {f : ℝ → ℝ}, ContinuousOn f (Icc p.T (2 * p.T)) →
      ContinuousOn (fun q : ℝ × ℝ => f q.1) (sqI p) := fun hf =>
    hf.comp continuous_fst.continuousOn fun q hq => hq.1
  have hsnd : ∀ {f : ℝ → ℝ}, ContinuousOn f (Icc p.T (2 * p.T)) →
      ContinuousOn (fun q : ℝ × ℝ => f q.2) (sqI p) := fun hf =>
    hf.comp continuous_snd.continuousOn fun q hq => hq.2
  have hM1c : ContinuousOn (fun q : ℝ × ℝ => rho p F q.1 / gwt p q.1 * gwt p q.2) (sqI p) :=
    (hfst hρg).mul (hsnd hgc)
  have hM2c : ContinuousOn (fun q : ℝ × ℝ => gwt p q.1 * (rho p F q.2 / gwt p q.2)) (sqI p) :=
    (hfst hgc).mul (hsnd hρg)
  have hcpt : IsCompact (sqI p) := isCompact_sqI
  have hM1i : IntegrableOn (fun q : ℝ × ℝ => rho p F q.1 / gwt p q.1 * gwt p q.2) (sqI p) :=
    hM1c.integrableOn_compact hcpt
  have hM2i : IntegrableOn (fun q : ℝ × ℝ => gwt p q.1 * (rho p F q.2 / gwt p q.2)) (sqI p) :=
    hM2c.integrableOn_compact hcpt
  have hfi : IntegrableOn (majK1 p F ν) (sqI p) := by
    have hνa : ContinuousOn (fun τ => |ν τ|) (Icc p.T (2 * p.T)) := hνc.abs.continuousOn
    have hc : ContinuousOn (majK1 p F ν) (sqI p) := by
      have := ((hM1c.add hM2c).const_smul (p.L ^ 2)).mul ((hfst hνa).mul (hsnd hνa))
      refine this.congr fun q hq => ?_
      simp only [majK1, Pi.smul_apply, Pi.add_apply, Pi.mul_apply, smul_eq_mul]
    exact hc.integrableOn_compact hcpt
  -- ∫_{sqI} majK1 ≤ L²B²(RG + GR)
  have hmain : ∫ q in sqI p, majK1 p F ν q ≤ p.L ^ 2 * B ^ 2 * (R * G + G * R) := by
    have step2 : ∫ q in sqI p, majK1 p F ν q
        ≤ ∫ q in sqI p, p.L ^ 2 * B ^ 2 *
          (rho p F q.1 / gwt p q.1 * gwt p q.2 + gwt p q.1 * (rho p F q.2 / gwt p q.2)) := by
      refine setIntegral_mono_on hfi ((hM1i.add hM2i).const_mul _) measurableSet_sqI
        fun q hq => majK1_le hF hν hT0 hq
    have step3 : ∫ q in sqI p, p.L ^ 2 * B ^ 2 *
          (rho p F q.1 / gwt p q.1 * gwt p q.2 + gwt p q.1 * (rho p F q.2 / gwt p q.2))
        = p.L ^ 2 * B ^ 2 * (R * G + G * R) := by
      rw [integral_const_mul, integral_add hM1i hM2i]
      congr 1
      unfold sqI
      rw [Measure.volume_eq_prod, setIntegral_prod_mul (fun τ => rho p F τ / gwt p τ) (gwt p),
        setIntegral_prod_mul (gwt p) (fun τ => rho p F τ / gwt p τ)]
      rfl
    linarith
  -- numerics
  have hcw : (cϱ / p.w) ^ 2 ≤ cϱ ^ 2 := by
    have : cϱ / p.w ≤ cϱ := div_le_self (by linarith) hw1
    have : 0 ≤ cϱ / p.w := by positivity
    nlinarith
  have hh : (p.h)⁻¹ = p.L / (2 * π) := by unfold Setting.h; rw [inv_div]
  have hhL : (p.h)⁻¹ ≤ p.L := by
    rw [hh, div_le_iff₀ (by positivity)]; nlinarith
  have hRle : R ≤ (90 + 32 * cϱ ^ 2) * (p.L * (p.L + p.l)) := by
    have hlog0 : 0 ≤ Real.log p.T := Real.log_nonneg hT1
    have h1 : (p.h)⁻¹ * (32 * p.L + 4 / 3 * (cϱ / p.w) ^ 2 * Real.log p.T)
        ≤ p.L * (32 * p.L + 4 / 3 * cϱ ^ 2 * (2 * p.l)) := by
      apply mul_le_mul hhL _ (by positivity) hL0.le
      gcongr
    set M := p.L * (p.L + p.l) with hM
    have hLL : p.L ^ 2 ≤ M := by rw [hM]; nlinarith
    have hLl' : p.L * p.l ≤ M := by rw [hM]; nlinarith
    have hM1 : 1 ≤ M := by rw [hM]; nlinarith
    have hc2 : cϱ ^ 2 ≤ cϱ ^ 2 * M := by nlinarith [sq_nonneg cϱ]
    have hc3 : cϱ ^ 2 * (p.L * p.l) ≤ cϱ ^ 2 * M := mul_le_mul_of_nonneg_left hLl' (sq_nonneg _)
    nlinarith
  calc ∫ q in sqI p, majK1 p F ν q ≤ p.L ^ 2 * B ^ 2 * (R * G + G * R) := hmain
    _ = 2 * (p.L ^ 2 * B ^ 2) * (R * G) := by ring
    _ ≤ 2 * (p.L ^ 2 * B ^ 2) * ((90 + 32 * cϱ ^ 2) * (p.L * (p.L + p.l)) * 2) := by
        gcongr
    _ = 4 * (90 + 32 * cϱ ^ 2) * (p.L ^ 3 * B ^ 2 * (p.L + p.l)) := by ring

end Bounds

section BoundsCor
variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}

/-- `|𝓔₁(ν)| ≤ ∬_{I×I} majK1(ν)`. -/
theorem abs_calE1_le_maj (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F) (_hT : 0 < p.T) :
    |calE1 p F ν| ≤ ∫ q in sqI p, majK1 p F ν q := by
  have hcpt : IsCompact (sqI p) := isCompact_sqI
  have hfi : IntegrableOn (fun q => trG2integrand p F ν q - KinfIntegrand p F ν q) (sqI p) :=
    ((trG2integrand_continuous hνc hF).sub (KinfIntegrand_continuous hνc hF)).continuousOn
      |>.integrableOn_compact hcpt
  -- integrability of majK1 on the compact square
  have hρc : Continuous (rho p F) := by
    have := hF.phiHat_cont; unfold rho; fun_prop
  have hdistc : Continuous (distB p) := by unfold distB; fun_prop
  have hgc : ContinuousOn (gwt p) (Icc p.T (2 * p.T)) := by
    unfold gwt
    refine ContinuousOn.inv₀ (by fun_prop) fun τ hτ => ?_
    have := distB_nonneg (p := p) hτ; positivity
  have hρg : ContinuousOn (fun τ => rho p F τ / gwt p τ) (Icc p.T (2 * p.T)) :=
    hρc.continuousOn.div hgc fun τ hτ => (gwt_pos hτ).ne'
  have hfst : ∀ {f : ℝ → ℝ}, ContinuousOn f (Icc p.T (2 * p.T)) →
      ContinuousOn (fun q : ℝ × ℝ => f q.1) (sqI p) := fun hf =>
    hf.comp continuous_fst.continuousOn fun q hq => hq.1
  have hsnd : ∀ {f : ℝ → ℝ}, ContinuousOn f (Icc p.T (2 * p.T)) →
      ContinuousOn (fun q : ℝ × ℝ => f q.2) (sqI p) := fun hf =>
    hf.comp continuous_snd.continuousOn fun q hq => hq.2
  have hνa : ContinuousOn (fun τ => |ν τ|) (Icc p.T (2 * p.T)) := hνc.abs.continuousOn
  have hM1c : ContinuousOn (fun q : ℝ × ℝ => rho p F q.1 / gwt p q.1 * gwt p q.2) (sqI p) :=
    (hfst hρg).mul (hsnd hgc)
  have hM2c : ContinuousOn (fun q : ℝ × ℝ => gwt p q.1 * (rho p F q.2 / gwt p q.2)) (sqI p) :=
    (hfst hgc).mul (hsnd hρg)
  have hc : ContinuousOn (majK1 p F ν) (sqI p) := by
    have := ((hM1c.add hM2c).const_smul (p.L ^ 2)).mul ((hfst hνa).mul (hsnd hνa))
    refine this.congr fun q hq => ?_
    simp only [majK1, Pi.smul_apply, Pi.add_apply, Pi.mul_apply, smul_eq_mul]
  have hmi : IntegrableOn (majK1 p F ν) (sqI p) := hc.integrableOn_compact hcpt
  unfold calE1
  have step1 := norm_integral_le_integral_norm (μ := volume.restrict (sqI p))
    (fun q => trG2integrand p F ν q - KinfIntegrand p F ν q)
  rw [Real.norm_eq_abs] at step1
  refine step1.trans ?_
  refine setIntegral_mono_on hfi.norm hmi measurableSet_sqI fun q hq => ?_
  rw [Real.norm_eq_abs]
  exact abs_E1integrand_le_majK1 hF hq

variable (cϱ lam : ℝ)

/-- **Bound for 𝓔₁** (cf. §5.3): `|𝓔₁| ≤ C · L³ B² l` for `T ≥ T₀` (corollary). -/
theorem calE1_bound :
    ∃ C T₀ : ℝ, ∀ (p : Setting) (F : LocalFun) (B : ℝ) (ν : ℝ → ℝ), p.lam = lam → T₀ ≤ p.T →
      LocalHypsCoreW cϱ p F → p.L ≤ 2 * p.l → Continuous ν → NuBound p B ν →
      |calE1 p F ν| ≤ C * (p.L ^ 3 * B ^ 2 * p.l) := by
  obtain ⟨C, T₀, h⟩ := calE1_maj_bound cϱ lam
  refine ⟨C, max T₀ 1, fun p F B ν hplam hT hF hL2l hνc hν => ?_⟩
  have hT0 : T₀ ≤ p.T := (le_max_left _ _).trans hT
  have hTpos : 0 < p.T := by linarith [(le_max_right T₀ 1).trans hT]
  exact (abs_calE1_le_maj hνc hF hTpos).trans (h p F B ν hplam hT0 hF hL2l hνc hν)

end BoundsCor

end PrimeSide
end Zeta23
