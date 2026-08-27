/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Hardy/EFLitCorrW.lean — the W explicit formula in "literature form with correction" on a line
Re s = c, 1 < c ≤ 5/4.  [XF′ Prop 9.1 + Thm 9.2 (a)]:
   Σ'_{ρ ∈ 𝒩_W} m_ρ h_k(γ_ρ) = literatureRHSW k + JcorrW c k − Σ_{ρ ∈ E₀} m_ρ H(ρ),
   literatureRHSW k = literatureRHS k + (H(0) + H(1))   (pole weight 2; GramBridgeW),
   JcorrW c k := (1/2π) ∫ [H(c+it) + H(1−c−it)]·(E₂′/E₂)(c+it) dt,
from three inputs taken as Props (discharged in Hardy/EFMain.lean): the full-line identity for
F_𝒵 = L₂ + W′/W, the L₋-line identity (1/2π)∫[H+H̃](L − L₂) = ½(H(0)+H(1)),
and the line facts for E₂; plus the c-generic ζ-side evaluation (1/2π)∫[H+H̃]·E = literatureRHS k
(ExplicitFormula/LitCorr.Efn_line_identity, with HwC and its integrability helpers).
Pointwise on the line: F_𝒵 = E₂ + E₂′/E₂ (EFBasic.FZfn_eq) and E₂ = E − (L − L₂) (EFBasic.E2fn_eq_Efn_add).
-/
import Zeta23.XiPrime.Hardy.EFBasic
import Zeta23.XiPrime.Hardy.GramBridgeW
import Zeta23.XiPrime.ExplicitFormula.LitCorr

open scoped BigOperators ArithmeticFunction ComplexConjugate
open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Zeta23
namespace XiPrime

open Hardy
open Zeta23.WeilEF (Hfn Hfn_mirror prime_side_line norm_Hfn_le continuous_Hfn_line
  integrable_Hfn_mul_logDeriv_zeta integrable_Hfn_mul_logDeriv_Gammaℝ)

/-! ## objects on the line Re s = c -/

/-- E₂′/E₂ on the line. -/
def dE2 (c : ℝ) (t : ℝ) : ℂ := deriv E2fn ((c:ℂ) + t * I) / E2fn ((c:ℂ) + t * I)

/-- the W correction functional JcorrW c k := (1/2π) ∫ [H(c+it)+H(1−c−it)]·(E₂′/E₂)(c+it) dt. -/
def JcorrW (c : ℝ) (k : ℝ → ℂ) : ℂ := (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, HwC c k t * dE2 c t

/-! ## the three input Props -/

/-- The full-line identity for F_𝒵 = L₂ + W′/W with a GIVEN finite low-zero set E₀. -/
def WFullLineIdentityWith {t₀ : ℝ} (hZ : WZerosInStrip t₀) (hs : WSeam t₀) (c : ℝ) (E₀ : Finset ℂ) : Prop :=
  ∀ (k : ℝ → ℂ), ContDiff ℝ 2 k → HasCompactSupport k →
    Summable (fun ρ : (wZeros hZ hs).carrier => (wMult (ρ : ℂ) : ℂ) * Hfn k ρ) ∧
    (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, (Hfn k ((c:ℂ) + t * I) + Hfn k (1 - c - t * I))
        * (L2 ((c:ℂ) + t * I) + logDeriv hardyW ((c:ℂ) + t * I)))
      = (∑' ρ : (wZeros hZ hs).carrier, (wMult (ρ : ℂ) : ℂ) * Hfn k ρ)
        + (∑ ρ ∈ E₀, (analyticOrderNatAt hardyW ρ : ℂ) * Hfn k ρ)
        - (3/2 : ℂ) * (Hfn k 0 + Hfn k 1)

/-- The full-line identity for F_𝒵 = L₂ + W′/W, with the finite low-zero set E₀. -/
def WFullLineIdentity {t₀ : ℝ} (hZ : WZerosInStrip t₀) (hs : WSeam t₀) (c : ℝ) : Prop :=
  ∃ E₀ : Finset ℂ, (∀ ρ ∈ E₀, |ρ.im| < t₀ ∧ 1 - c < ρ.re ∧ ρ.re < c) ∧ WFullLineIdentityWith hZ hs c E₀

/-- The L₋-line identity. -/
def LminusLineIdentity (c : ℝ) : Prop :=
  ∀ (k : ℝ → ℂ), ContDiff ℝ 2 k → HasCompactSupport k →
    Integrable (fun t : ℝ => (Hfn k ((c:ℂ) + t * I) + Hfn k (1 - c - t * I))
        * (Lfn ((c:ℂ) + t * I) - L2 ((c:ℂ) + t * I))) ∧
    (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, (Hfn k ((c:ℂ) + t * I) + Hfn k (1 - c - t * I))
        * (Lfn ((c:ℂ) + t * I) - L2 ((c:ℂ) + t * I)))
      = (1/2 : ℂ) * (Hfn k 0 + Hfn k 1)

/-- The E₂ facts on the whole line Re s = c (for the chosen c). -/
structure E2LineFacts (c : ℝ) : Prop where
  W_ne : ∀ t : ℝ, hardyW ((c:ℂ) + t * I) ≠ 0
  bound : ∃ CE : ℝ, 0 ≤ CE ∧ ∀ t : ℝ, ‖dE2 c t‖ ≤ CE
  cont : Continuous (dE2 c)

/-! ## the W explicit formula, literature form with correction -/

theorem Hfn_zero_one_eq (k : ℝ → ℂ) : Hfn k 0 + Hfn k 1 = paperFT k (I / 2) + paperFT k (-I / 2) := by
  have hpole0 : Hfn k 0 = paperFT k (I / 2) := by
    unfold Hfn; congr 1
    rw [div_eq_iff Complex.I_ne_zero, div_mul_eq_mul_div, Complex.I_mul_I]; norm_num
  have hpole1 : Hfn k 1 = paperFT k (-I / 2) := by
    unfold Hfn; congr 1
    rw [div_eq_iff Complex.I_ne_zero]
    rw [show (-I / 2) * I = -(I * I) / 2 by ring, Complex.I_mul_I]; norm_num
  rw [hpole0, hpole1]

/-- pointwise on the line: F_𝒵 = E − (L − L₂) + E₂′/E₂. -/
theorem FZfn_line_split {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 5/4) (hW : ∀ t : ℝ, hardyW ((c:ℂ) + t * I) ≠ 0)
    (t : ℝ) :
    L2 ((c:ℂ) + t * I) + logDeriv hardyW ((c:ℂ) + t * I)
      = Efn ((c:ℂ) + t * I) - (Lfn ((c:ℂ) + t * I) - L2 ((c:ℂ) + t * I)) + dE2 c t := by
  have hs : ((c:ℂ) + t * I) ∈ GoodStrip := by
    constructor <;> simp <;> linarith
  have h := FZfn_eq hs (hW t)
  rw [FZfn] at h
  rw [h, dE2, E2fn_eq_Efn_add]; ring

/-- **the W explicit formula, literature form with correction** (see file header). -/
theorem w_EF_lit_corr {t₀ c : ℝ} {hZ : WZerosInStrip t₀} {hs : WSeam t₀} (hc1 : 1 < c) (hc2 : c ≤ 5/4)
    {E₀ : Finset ℂ} (hWL' : WFullLineIdentityWith hZ hs c E₀) (hLm : LminusLineIdentity c) (hE2 : E2LineFacts c)
    {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    Summable (fun ρ : (wZeros hZ hs).carrier => (wMult (ρ : ℂ) : ℂ) * paperFT k (gammaOf ρ)) ∧
    ∑' ρ : (wZeros hZ hs).carrier, (wMult (ρ : ℂ) : ℂ) * paperFT k (gammaOf ρ)
      = literatureRHSW k + JcorrW c k - ∑ ρ ∈ E₀, (analyticOrderNatAt hardyW ρ : ℂ) * Hfn k ρ := by
  have hgammaOf : ∀ ρ : ℂ, paperFT k (gammaOf ρ) = Hfn k ρ := fun ρ => rfl
  simp_rw [hgammaOf]
  obtain ⟨hsum, hfull⟩ := hWL' k hk hkc
  refine ⟨hsum, ?_⟩
  obtain ⟨hintLm, hLmv⟩ := hLm k hk hkc
  obtain ⟨hintE, hEv⟩ := Efn_line_identity hc1 (by linarith) hk hkc
  obtain ⟨CE, -, hCE⟩ := hE2.bound
  have hintJ : Integrable (fun t : ℝ => HwC c k t * dE2 c t) :=
    integrable_HwC_mul_bdd hc1 (by linarith) hk hkc hE2.cont hCE
  have hintLm' : Integrable (fun t : ℝ => HwC c k t * (Lfn ((c:ℂ) + t * I) - L2 ((c:ℂ) + t * I))) := hintLm
  -- split the F_𝒵 line integral
  have e : ∀ t : ℝ, HwC c k t * (L2 ((c:ℂ) + t * I) + logDeriv hardyW ((c:ℂ) + t * I))
      = HwC c k t * Efn ((c:ℂ) + t * I) - HwC c k t * (Lfn ((c:ℂ) + t * I) - L2 ((c:ℂ) + t * I))
        + HwC c k t * dE2 c t := by
    intro t; rw [FZfn_line_split hc1 hc2 hE2.W_ne t]; ring
  have hfull' : (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, HwC c k t * (L2 ((c:ℂ) + t * I) + logDeriv hardyW ((c:ℂ) + t * I)))
      = (∑' ρ : (wZeros hZ hs).carrier, (wMult (ρ : ℂ) : ℂ) * Hfn k ρ)
        + (∑ ρ ∈ E₀, (analyticOrderNatAt hardyW ρ : ℂ) * Hfn k ρ) - (3/2 : ℂ) * (Hfn k 0 + Hfn k 1) := hfull
  simp_rw [e] at hfull'
  have hA : Integrable (fun t : ℝ => HwC c k t * Efn ((c:ℂ) + t * I)
      - HwC c k t * (Lfn ((c:ℂ) + t * I) - L2 ((c:ℂ) + t * I))) := hintE.sub hintLm'
  rw [integral_add hA hintJ, integral_sub hintE hintLm'] at hfull'
  have hLmv' : (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, HwC c k t * (Lfn ((c:ℂ) + t * I) - L2 ((c:ℂ) + t * I)))
      = (1/2 : ℂ) * (Hfn k 0 + Hfn k 1) := hLmv
  rw [literatureRHSW_eq, ← Hfn_zero_one_eq, JcorrW]
  -- linear algebra on hfull'
  have key : (∑' ρ : (wZeros hZ hs).carrier, (wMult (ρ : ℂ) : ℂ) * Hfn k ρ)
      = (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, HwC c k t * Efn ((c:ℂ) + t * I))
        - (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, HwC c k t * (Lfn ((c:ℂ) + t * I) - L2 ((c:ℂ) + t * I)))
        + (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, HwC c k t * dE2 c t)
        - (∑ ρ ∈ E₀, (analyticOrderNatAt hardyW ρ : ℂ) * Hfn k ρ) + (3/2 : ℂ) * (Hfn k 0 + Hfn k 1) := by
    linear_combination -hfull'
  rw [key, hEv, hLmv']
  ring

end XiPrime
end Zeta23
