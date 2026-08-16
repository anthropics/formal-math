/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.Assembly.SeamMult
import Zeta23.ZeroSide.Union

/-!
# Finite-compression seam for the simple-or-on-line union
-/

open RHLinalg

noncomputable section

namespace Zeta23.Assembly

/-- Interval additivity of the direct union count. -/
theorem Nu_add (Z : ZeroConfig) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    Z.Nu a c = Z.Nu a b + Z.Nu b c := by
  unfold ZeroConfig.Nu
  rw [window_union Z hab hbc, finsum_mem_union (window_disjoint Z a b c)
    (Z.window_finite a b) (Z.window_finite b c)]

/-- The union count is bounded by total multiplicity. -/
theorem Nu_le_N (Z : ZeroConfig) (a b : ℝ) : Z.Nu a b ≤ Z.N a b := by
  have h := Z.N_eq_Nu_add_Nbad a b
  omega

/-- Enlarging the interval costs at most the total tail multiplicity. -/
theorem NuIprime_le (Z : ZeroConfig) {T : ℝ} (hT : 0 ≤ T) :
    Z.NuIprime T ≤ Z.Nu T (2 * T) + NII Z T := by
  unfold ZeroConfig.NuIprime
  have h0 := D0_nonneg T
  rw [Nu_add Z (b := T) (by linarith) (by linarith),
    Nu_add Z (a := T) (b := 2 * T) (by linarith) (by linarith)]
  have h1 := Nu_le_N Z (T - D0 T) T
  have h2 := Nu_le_N Z (2 * T) (2 * T + D0 T)
  unfold NII
  omega

variable {Z : ZeroConfig} {P : Params} {T : ℝ}

/-- **Union seam A.**  The generic tail perturbation preserves the coefficient
`2(2+√2)`; the enlarged-window bookkeeping costs `2 unionQ · NII`. -/
theorem seamA_union (hT : 0 ≤ T) (hconj : ZeroSide.PhiHatConj T P)
    (hreal : ZeroSide.PhiHatReal T P) (hPois : ZeroSide.PoissonSq T P)
    {θ₀ : ℝ} (hTl : TailInputs Z P T θ₀) (ha : 0 < P.a T) (hL : 0 < P.L T) :
    2 * ZeroSide.unionC * rtrace (P.hat T (Z.Gz P T)) -
        frobSq (P.hat T (Z.Gz P T)) -
        ZeroSide.unionQ * (Z.N T (2 * T) : ℝ) -
        2 * ZeroSide.unionQ * (NII Z T : ℝ) -
        θ₀ / (P.a T * P.L T) *
          (2 * ZeroSide.unionC +
            2 * Real.sqrt (frobSq (P.hat T (Z.Gz P T))) +
            θ₀ / (P.a T * P.L T))
      ≤ ZeroSide.unionQ * (Z.Nu T (2 * T) : ℝ) := by
  obtain ⟨Bc, hB0, htrE, hfrE, hBle⟩ := hTl.hat
  have hGAE : P.hat T (Z.Gz P T) =
      P.hat T (Z.Az P T) + P.hat T (Z.Ez P T) := by
    rw [← hat_add]
    congr 1
    simp [ZeroConfig.Ez]
  have hB₀ : 0 ≤ θ₀ / (P.a T * P.L T) :=
    div_nonneg hTl.theta_nonneg (mul_pos ha hL).le
  have hcore := ZeroSide.hatAz_union Z T P hconj hreal hPois (by positivity)
  have hpert := ctr_sub_frobSq_perturb (2 * ZeroSide.unionC)
    (mul_nonneg (by norm_num) ZeroSide.unionC_pos.le) hGAE hB₀
    (htrE.trans hBle) (hfrE.trans (pow_le_pow_left₀ hB0 hBle 2))
  have hNu : (Z.NuIprime T : ℝ) ≤
      (Z.Nu T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast NuIprime_le Z hT
  have hNI : (Z.NIprime T : ℝ) =
      (Z.N T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast NIprime_eq Z hT
  rw [hNI] at hcore
  have hq := ZeroSide.unionQ_pos
  nlinarith [hcore, hpert, mul_le_mul_of_nonneg_left hNu hq.le]

end Zeta23.Assembly
