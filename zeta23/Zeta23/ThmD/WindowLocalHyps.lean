/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmD/WindowLocalHyps.lean — every admissible window satisfies `LocalHypsCore`.  Assembly of Zeta23/ThmD/WindowCore.lean (Fourier/Poisson side) and
Zeta23/ThmD/PsiC.lean (ψ-majorant integrals), field by field; `b ≥ 1/2` is an input (it is a
property of the particular window — for `φ_D` it holds for large `T`, see BridgeD.lean).
-/
import Zeta23.ThmD.WindowCore
import Zeta23.ThmD.PsiC

noncomputable section

open Real Set MeasureTheory

namespace Zeta23
namespace AdmWindow

/-- **Admissible window ⇒ `LocalHypsCore`.**  For any `p : Setting` in the regime
(`0 < λ ≤ 1`, `l ≥ 1`, `X ≥ 1`) and any window `v` admissible at scale `(p.L, p.w)` with constant
`c` and `b_v ≥ 1/2`, the local data `(v̂, V, A_v, g_v, a_v, b_v)` satisfy all of §5's hypotheses. -/
theorem localHypsCore {v : ℝ → ℝ} {c : ℝ} (p : PrimeSide.Setting) (hW : AdmWindow v p.L p.w c)
    (hlam : 0 < p.lam) (hlam1 : p.lam ≤ 1) (hl : 1 ≤ p.l) (hX : 1 ≤ p.X)
    (hb : 1 / 2 ≤ bv v p.L) :
    PrimeSide.LocalHypsCore c p (localFun v p.L) := by
  have hc := hW.four_le_c
  have hw := hW.one_le_w
  have hwL := hW.w8
  have hcw : 0 ≤ c / p.w := div_nonneg hW.c_nonneg hW.w_pos.le
  have hψ1 : ∀ r, |vHatR v r| ≤ PsiC.psiC c p.L p.w r := fun r => by
    rw [PsiC.psiC_eq_psiA]; exact hW.abs_vHatR_le_psiA p rfl rfl r
  have hψ2 : ∀ r, |VPhiR v r| ≤ PsiC.psiC c p.L p.w r := fun r => by
    rw [PsiC.psiC_eq_psiA]; exact hW.abs_VPhiR_le_psiA p rfl rfl r
  exact {
    four_le_cϱ := hc
    lam_pos := hlam
    lam_le_one := hlam1
    one_le_w := hw
    w_le := by linarith
    one_le_l := hl
    phiHat_cont := hW.vHatR_continuous
    phiHat_even := hW.vHatR_even
    phiHat_le_L := hW.abs_vHatR_le_L
    phiHat_le_inv := hW.abs_vHatR_mul_abs_le
    phiHat_le_sq := hW.abs_vHatR_mul_sq_le
    phiHat_sq_integrable := hW.integrable_vHatR_sq
    phiHat_sq_mul_abs_integrable := hW.integrable_vHatR_sq_mul_abs
    integral_phiHat_sq_mul_abs_le := PsiC.integral_sq_mul_abs_le_of_le_psi hc hw hwL hψ1
    phiHat_sq_mul_sq_integrable :=
      PsiC.integrable_sq_mul_sq_of_bounds hW.vHatR_continuous hcw hW.abs_vHatR_mul_abs_le
        hW.abs_vHatR_mul_sq_le
    integral_phiHat_sq_mul_sq_le :=
      PsiC.integral_sq_mul_sq_le_of_bounds hcw hW.abs_vHatR_mul_abs_le hW.abs_vHatR_mul_sq_le
    phiHat_sq_integral := hW.integral_vHatR_sq
    phiHat_sq_fourier := hW.integral_vHatR_sq_mul_cos
    g_nonneg := hW.gv_nonneg
    g_le_Aphi := hW.gv_le_Av
    Aphi_le := hW.Av_le
    Phi_contDiff := hW.VPhiR_contDiff_one
    Phi_even := hW.VPhiR_even
    Phi_le_L := hW.abs_VPhiR_le_L
    Phi_le_inv := hW.abs_VPhiR_mul_abs_le
    Phi_le_sq := hW.abs_VPhiR_mul_sq_le
    Phi_sq_integrable := hW.integrable_VPhiR_sq
    Phi_sq_mul_abs_integrable := hW.integrable_VPhiR_sq_mul_abs
    integral_Phi_sq_mul_abs_le := PsiC.integral_sq_mul_abs_le_of_le_psi hc hw hwL hψ2
    Phi_sq_mul_sq_integrable :=
      PsiC.integrable_sq_mul_sq_of_bounds hW.VPhiR_continuous hcw hW.abs_VPhiR_mul_abs_le
        hW.abs_VPhiR_mul_sq_le
    integral_Phi_sq_mul_sq_le :=
      PsiC.integral_sq_mul_sq_le_of_bounds hcw hW.abs_VPhiR_mul_abs_le hW.abs_VPhiR_mul_sq_le
    Phi_zero := hW.VPhiR_zero
    Phi_sq_integral := hW.integral_VPhiR_sq
    Phi_sq_fourier := hW.integral_VPhiR_sq_mul_cos
    poisson := fun τ τ' => hW.hasSum_vHatR_mul p.T τ τ'
    b_ge_half := hb
    b_le_a := hW.bv_le_av
    a_le_one := hW.av_le_one
    psi_integrable := by
      rw [← PsiC.psiC_eq_psiA]; exact PsiC.psi_integrable hc hw hwL
    psi_sq_integrable := by
      rw [← PsiC.psiC_eq_psiA]; exact PsiC.psi_sq_integrable hc hw hwL
    integral_psi_Ioi_le := by
      rw [← PsiC.psiC_eq_psiA]; exact PsiC.integral_psi_Ioi_le hc hw hwL
    integral_psi_sq_le := by
      rw [← PsiC.psiC_eq_psiA]; exact PsiC.integral_psi_sq_le hc hw hwL
    phiHat_le_psi := hW.abs_vHatR_le_psiA p rfl rfl
    Phi_le_psi := hW.abs_VPhiR_le_psiA p rfl rfl
    PiX_cont := PiX_continuous p.X_pos
    PiX_bound := PiX_abs_le hX }

end AdmWindow
end Zeta23

end
