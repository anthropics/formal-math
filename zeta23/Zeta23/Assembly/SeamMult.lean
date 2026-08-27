/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Assembly/SeamMult.lean — seams A for the multiplicity-aware rank–trace variants.  Decorates `hatAz_mult2/3` (Zeta23/ZeroSide/Mult.lean) with the
seamA pattern: Â → Ĝ = Â + Ê (tail perturbation, c-generic) and I′ → (T,2T] windows.  Conclusions:
  seamA_mult2 : 4trĜ − ‖Ĝ‖² − 2N − 3·NII − B(4 + 2√‖Ĝ‖² + B) ≤ N₀ˢ(T,2T)      [c = 2]
  seamA_mult3 : 6trĜ − ‖Ĝ‖² − 3N − 5·NII − B(6 + 2√‖Ĝ‖² + B) ≤ 2·N_d(T,2T)   [c = 3]
feeding Assembly/Certificate's count_certificate (c=2) and count_certificate_c3.
-/
import Zeta23.Assembly
import Zeta23.ZeroSide.Mult

open RHLinalg

noncomputable section

namespace Zeta23
namespace Assembly

variable {n : Type*} [Fintype n] [DecidableEq n] {𝕜 : Type*} [RCLike 𝕜]

/-- c-generic version of `four_tr_sub_frobSq_perturb`. -/
theorem ctr_sub_frobSq_perturb {Ghat Ahat Ehat : Matrix n n 𝕜} (c : ℝ) (hc : 0 ≤ c)
    (hGAE : Ghat = Ahat + Ehat) {B : ℝ} (hB : 0 ≤ B)
    (htrE : |rtrace Ehat| ≤ B) (hfrE : frobSq Ehat ≤ B ^ 2) :
    c * rtrace Ghat - frobSq Ghat - B * (c + 2 * Real.sqrt (frobSq Ghat) + B)
      ≤ c * rtrace Ahat - frobSq Ahat := by
  have hA : Ahat = Ghat - Ehat := by rw [hGAE]; abel
  have htr : rtrace Ahat = rtrace Ghat - rtrace Ehat := by rw [hA, rtrace_sub]
  have hsqE : Real.sqrt (frobSq Ehat) ≤ B := Real.sqrt_le_iff.mpr ⟨hB, hfrE⟩
  have hsqG : 0 ≤ Real.sqrt (frobSq Ghat) := Real.sqrt_nonneg _
  have hfrA : frobSq Ahat ≤ (Real.sqrt (frobSq Ghat) + B) ^ 2 := by
    rw [hA]
    refine (frobSq_sub_le Ghat Ehat).trans ?_
    gcongr
  have habs := abs_le.mp htrE
  have hGsq : Real.sqrt (frobSq Ghat) ^ 2 = frobSq Ghat := Real.sq_sqrt (frobSq_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left habs.1 hc, sq_nonneg (Real.sqrt (frobSq Ghat) + B)]

variable {Z : ZeroConfig} {P : Params} {T : ℝ}

/-- **Seam A, multiplicity-aware, c = 2**: the seamA shape with conclusion N₀ˢ. -/
theorem seamA_mult2 (hT : 0 ≤ T) (hconj : ZeroSide.PhiHatConj T P)
    (hreal : ZeroSide.PhiHatReal T P) (hPois : ZeroSide.PoissonSq T P)
    {θ₀ : ℝ} (hTl : TailInputs Z P T θ₀) (ha : 0 < P.a T) (hL : 0 < P.L T) :
    4 * rtrace (P.hat T (Z.Gz P T)) - frobSq (P.hat T (Z.Gz P T)) - 2 * (Z.N T (2 * T) : ℝ)
      - 3 * (NII Z T : ℝ)
      - θ₀ / (P.a T * P.L T)
          * (4 + 2 * Real.sqrt (frobSq (P.hat T (Z.Gz P T))) + θ₀ / (P.a T * P.L T))
      ≤ Z.N0s T (2 * T) := by
  obtain ⟨Bc, hB0, htrE, hfrE, hBle⟩ := hTl.hat
  have hGAE : P.hat T (Z.Gz P T) = P.hat T (Z.Az P T) + P.hat T (Z.Ez P T) := by
    rw [← hat_add]; congr 1; simp [ZeroConfig.Ez]
  have hB₀ : 0 ≤ θ₀ / (P.a T * P.L T) := div_nonneg hTl.theta_nonneg (mul_pos ha hL).le
  have hcore := ZeroSide.hatAz_mult2 Z T P hconj hreal hPois (by positivity)
  have hpert := ctr_sub_frobSq_perturb 4 (by norm_num) hGAE hB₀ (htrE.trans hBle)
    (hfrE.trans (pow_le_pow_left₀ hB0 hBle 2))
  have hs1 : (Z.s1 T : ℝ) ≤ (Z.N0s T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast s1_le Z hT
  have hNI : (Z.NIprime T : ℝ) = (Z.N T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast NIprime_eq Z hT
  rw [hNI] at hcore
  linarith [hcore, hpert, hs1]

/-- **Seam A, multiplicity-aware, c = 3**: 6trĜ − ‖Ĝ‖² − 3N − 5NII − B(6+2√+B) ≤ 2·N_d. -/
theorem seamA_mult3 (hT : 0 ≤ T) (hconj : ZeroSide.PhiHatConj T P)
    (hreal : ZeroSide.PhiHatReal T P) (hPois : ZeroSide.PoissonSq T P)
    {θ₀ : ℝ} (hTl : TailInputs Z P T θ₀) (ha : 0 < P.a T) (hL : 0 < P.L T) :
    6 * rtrace (P.hat T (Z.Gz P T)) - frobSq (P.hat T (Z.Gz P T)) - 3 * (Z.N T (2 * T) : ℝ)
      - 5 * (NII Z T : ℝ)
      - θ₀ / (P.a T * P.L T)
          * (6 + 2 * Real.sqrt (frobSq (P.hat T (Z.Gz P T))) + θ₀ / (P.a T * P.L T))
      ≤ 2 * (Z.Nd T (2 * T) : ℝ) := by
  obtain ⟨Bc, hB0, htrE, hfrE, hBle⟩ := hTl.hat
  have hGAE : P.hat T (Z.Gz P T) = P.hat T (Z.Az P T) + P.hat T (Z.Ez P T) := by
    rw [← hat_add]; congr 1; simp [ZeroConfig.Ez]
  have hB₀ : 0 ≤ θ₀ / (P.a T * P.L T) := div_nonneg hTl.theta_nonneg (mul_pos ha hL).le
  have hcore := ZeroSide.hatAz_mult3 Z T P hconj hreal hPois (by positivity)
  have hpert := ctr_sub_frobSq_perturb 6 (by norm_num) hGAE hB₀ (htrE.trans hBle)
    (hfrE.trans (pow_le_pow_left₀ hB0 hBle 2))
  have hZd : ((Z.ZIprime T).ncard : ℝ) ≤ (Z.Nd T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast card_ZIprime_le Z hT
  have hNI : (Z.NIprime T : ℝ) = (Z.N T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast NIprime_eq Z hT
  rw [hNI] at hcore
  linarith [hcore, hpert, hZd]

end Assembly
end Zeta23
