/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.Assembly
import Zeta23.ZeroSide.SextuplePenalty

/-!
# Seam A with the simple-zero sextuple penalty

This transports the strengthened simple-only zero-block inequality from
`Â = hat(Az)` to `Ĝ = hat(Gz)`, then changes the enlarged interval `I'` to
`(T, 2T]`.  Since `P₁` contains every simple on-line atom in `I'`, the collar
accounting is the same exact `3 * NII` loss as in `seamA_mult2`.
-/

open RHLinalg

noncomputable section

namespace Zeta23
namespace Assembly

variable {Z : ZeroConfig} {P : Params} {T : ℝ}

/-- **Seam A, sextuple-strengthened.**  The proof-free penalty is the spectral
sum on the Gram matrix of all normalized simple on-line columns in `I'`. -/
theorem seamA_sextuple (hT : 0 ≤ T) (hPois : ZeroSide.PoissonSq T P)
    {θ₀ : ℝ} (hTl : TailInputs Z P T θ₀) (ha : 0 < P.a T) (hL : 0 < P.L T) :
    4 * rtrace (P.hat T (Z.Gz P T)) - frobSq (P.hat T (Z.Gz P T))
      - 2 * (Z.N T (2 * T) : ℝ) - 3 * (NII Z T : ℝ)
      - θ₀ / (P.a T * P.L T)
          * (4 + 2 * Real.sqrt (frobSq (P.hat T (Z.Gz P T)))
            + θ₀ / (P.a T * P.L T))
      + ZeroSide.simpleSextuplePenalty Z T P
      ≤ Z.N0s T (2 * T) := by
  obtain ⟨B, hB0, htrE, hfrE, hBle⟩ := hTl.hat
  have hGAE : P.hat T (Z.Gz P T) =
      P.hat T (Z.Az P T) + P.hat T (Z.Ez P T) := by
    rw [← hat_add]
    congr 1
    simp [ZeroConfig.Ez]
  have hB₀ : 0 ≤ θ₀ / (P.a T * P.L T) :=
    div_nonneg hTl.theta_nonneg (mul_pos ha hL).le
  have hcore := ZeroSide.hatAz_sextuplePenalty Z T P hPois (by positivity)
  have hpert := four_tr_sub_frobSq_perturb hGAE hB₀
    (htrE.trans hBle) (hfrE.trans (pow_le_pow_left₀ hB0 hBle 2))
  have hs1 : (Z.s1 T : ℝ) ≤ (Z.N0s T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast s1_le Z hT
  have hNI : (Z.NIprime T : ℝ) =
      (Z.N T (2 * T) : ℝ) + (NII Z T : ℝ) := by
    exact_mod_cast NIprime_eq Z hT
  rw [hNI] at hcore
  linarith [hcore, hpert, hs1]

end Assembly
end Zeta23
