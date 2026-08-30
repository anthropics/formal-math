/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.XiPrime.Assembly
import Zeta23.XiPrime.PrimeSide.Moments
import Zeta23.XiPrime.Window
import Zeta23.XiPrime.Window.FlatAdm
import Zeta23.XiPrime.Window.Quartic
import Zeta23.XiPrime.QuarticWindow
import Zeta23.XiPrime.Transfer
import Zeta23.XiPrime.PrimeSide.Final
import Zeta23.XiPrime.Transfer.W
import Zeta23.XiPrime.Coeff.ReexpansionW
import Zeta23.XiPrime.Certificate.D1
import Zeta23.GammaFacts.Complete
import Zeta23.MV.Final

noncomputable section

open Filter Topology Set

namespace Zeta23
namespace XiPrime

/-- **P1 for the flat family at the tree's taper**, for any coefficient family with density D₁
(xiCoeffFamily and wCoeffFamily both qualify by rfl), from its (H1)–(H3) and prop:PP for P_c. -/
theorem coeffMoments_flat_D1 (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ)
    {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) {Fam : CoeffFamily} (hF : Fam.Hyps) (hD : Fam.D = D1) :
    CoeffMoments Z (fun _ => paramsOf ϱ lam) Fam (kappaXi lam vFlat) := by
  have hP := paramsOf_valid hϱ h0 h1.le
  have hD0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ D1 x := fun x hx => D1_nonneg hx.1
  have hc := tendsto_cRatio_flat (P := paramsOf ϱ lam) hP (continuousOn_D1 (Icc 0 1)) hD0
  have hc0 : 0 < cWin D1 lam vFlat := cWin_D1_vFlat_pos h0 h1.le
  have e : kappaXi lam vFlat = (cWin D1 lam vFlat)⁻¹ := one_div _
  rw [e]
  refine coeffMoments_flat (P := paramsOf ϱ lam) hP h1 (admFamily_taper hP) hF gammaFacts MV.mv_hilbert
    ppInput_of_PP hR hc0 ?_
  rw [hD]
  exact hc

/-- **P1 for the QUARTIC family** Pf := (paramsOf ϱ λ).atV vQuartic, any coefficient family with density D₁:
combines `coeffMoments_atV`, `admFamily_atV_quartic`, and `tendsto_cRatio_quartic_D1`. -/
theorem coeffMoments_quartic_D1 (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ)
    {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) {Fam : CoeffFamily} (hF : Fam.Hyps) (hD : Fam.D = D1) :
    CoeffMoments Z ((paramsOf ϱ lam).atV vQuartic) Fam (kappaXi lam vQuartic) := by
  have hP := paramsOf_valid hϱ h0 h1.le
  have hc := tendsto_cRatio_quartic_D1 (P := paramsOf ϱ lam) hP
  have hc0 : 0 < cWin D1 lam vQuartic := cWin_D1_vQuartic_pos h0 h1.le
  have e : kappaXi lam vQuartic = (cWin D1 lam vQuartic)⁻¹ := one_div _
  rw [e]
  refine coeffMoments_atV (P := paramsOf ϱ lam) hP h1 (admFamily_atV_quartic hP) hF gammaFacts MV.mv_hilbert
    ppInput_of_PP hR hc0 ?_
  rw [hD]
  exact hc

/-- P1 for ξ′, quartic window. -/
theorem coeffMoments_quartic_xi (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ)
    {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) (hF : xiCoeffFamily.Hyps) :
    CoeffMoments Z ((paramsOf ϱ lam).atV vQuartic) xiCoeffFamily (kappaXi lam vQuartic) :=
  coeffMoments_quartic_D1 Z hR hϱ h0 h1 hF rfl

/-- P1 for ξ′ (b_N = C(N; L_T)), flat window. -/
theorem coeffMoments_flat_xi (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ)
    {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) (hF : xiCoeffFamily.Hyps) :
    CoeffMoments Z (fun _ => paramsOf ϱ lam) xiCoeffFamily (kappaXi lam vFlat) :=
  coeffMoments_flat_D1 Z hR hϱ h0 h1 hF rfl

/-- P1 for Z′ (coefficients C(N; ½ l)), flat window. -/
theorem coeffMoments_flat_w (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ)
    {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) (hF : wCoeffFamily.Hyps) :
    CoeffMoments Z (fun _ => paramsOf ϱ lam) wCoeffFamily (kappaXi lam vFlat) :=
  coeffMoments_flat_D1 Z hR hϱ h0 h1 hF rfl

/-! ## P2 — the two-trace transfer, via xiTraceTransfer_of

Remaining inputs: the explicit formula XiEF Z Pf and the coefficient
re-expansion Reexpansion F e ρ₀ A T₀.  Everything else xiTraceTransfer_of
asks for is discharged here: P.Valid, λ/w constancy (rfl), LocalHypsCore eventually (flat:
localHypsCore_eventually ∘ admFamily_taper; quartic: localHypsCoreQ_eventually
transported along atV_toSetting / atV_localFun), H-Γ, a ≥ 1/2 (WindowZeroSide.a_half), H-RvM, and PPUpper
(frobSq_Ppart_le at PPInput := ppInput_of_PP, with H-MV := Zeta23.MV.mv_hilbert). -/

/-- **P2 for the flat family.** -/
theorem traceTransfer_flat (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ)
    {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) {F : CoeffFamily}
    (hEF : XiEF Z (fun _ => paramsOf ϱ lam))
    {e : ℝ → ℕ → ℕ → ℂ} {ρ₀ A T₀ : ℝ} (hρ₀ : 0 ≤ ρ₀) (hE : Reexpansion F e ρ₀ A T₀) :
    XiTraceTransfer Z (fun _ => paramsOf ϱ lam) F := by
  have hP := paramsOf_valid hϱ h0 h1.le
  obtain ⟨C, hC, hMV⟩ := MV.mv_hilbert
  have hW := windowZeroSide_flat Z hR (paramsOf ϱ lam) hP
  exact xiTraceTransfer_of Z (fun _ => paramsOf ϱ lam) F (paramsOf ϱ lam) hP h1 (fun _ => ⟨rfl, rfl⟩)
    (localHypsCore_eventually (win := fun T => (paramsOf ϱ lam).phi T) hP (admFamily_taper hP)) gammaFacts
    ⟨1 / 2, by norm_num, hW.a_half⟩ hR hEF hρ₀ hE
    (frobSq_Ppart_le ppInput_of_PP hMV hC _ _ ⟨h0, h1.le⟩)

/-- **P2 for the quartic family.** -/
theorem traceTransfer_quartic (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) {ϱ : ℝ → ℝ}
    (hϱ : TaperProfile ϱ) {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) {F : CoeffFamily}
    (hEF : XiEF Z ((paramsOf ϱ lam).atV vQuartic))
    {e : ℝ → ℕ → ℕ → ℂ} {ρ₀ A T₀ : ℝ} (hρ₀ : 0 ≤ ρ₀) (hE : Reexpansion F e ρ₀ A T₀) :
    XiTraceTransfer Z ((paramsOf ϱ lam).atV vQuartic) F := by
  have hP := paramsOf_valid hϱ h0 h1.le
  obtain ⟨C, hC, hMV⟩ := MV.mv_hilbert
  have hW := windowZeroSide_atV Z hR hP
  have hcore : ∃ T₁ : ℝ, ∀ T : ℝ, T₁ ≤ T → PrimeSide.LocalHypsCore (cQ (paramsOf ϱ lam).ϱ)
      (((paramsOf ϱ lam).atV vQuartic T).toSetting T) (((paramsOf ϱ lam).atV vQuartic T).localFun T) := by
    obtain ⟨T₁, hT₁⟩ := localHypsCoreQ_eventually hP
    refine ⟨T₁, fun T hT => ?_⟩
    rw [Params.atV_toSetting, Params.atV_localFun T hP vQuartic_even]
    exact hT₁ T hT
  exact xiTraceTransfer_of Z _ F (paramsOf ϱ lam) hP h1 (fun _ => ⟨rfl, rfl⟩) hcore gammaFacts
    ⟨1 / 2, by norm_num, hW.a_half⟩ hR hEF hρ₀ hE
    (frobSq_Ppart_le ppInput_of_PP hMV hC _ _ ⟨h0, h1.le⟩)

/-- **P2 for Z′ (W), flat family**, obtained from `wTraceTransfer_of` and `wReexpansion`; the one
remaining input is the W explicit formula `WEF Z Pf` (see StatementW.lean). -/
theorem traceTransfer_flat_w (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ)
    {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) (hEF : WEF Z (fun _ => paramsOf ϱ lam)) :
    XiTraceTransfer Z (fun _ => paramsOf ϱ lam) wCoeffFamily := by
  have hP := paramsOf_valid hϱ h0 h1.le
  obtain ⟨C, hC, hMV⟩ := MV.mv_hilbert
  obtain ⟨e, ρ₀, A, T₁, hρ₀, hE⟩ := wReexpansion
  have hW := windowZeroSide_flat Z hR (paramsOf ϱ lam) hP
  exact wTraceTransfer_of Z (fun _ => paramsOf ϱ lam) wCoeffFamily (paramsOf ϱ lam) hP h1
    (fun _ => ⟨rfl, rfl⟩)
    (localHypsCore_eventually (win := fun T => (paramsOf ϱ lam).phi T) hP (admFamily_taper hP)) gammaFacts
    ⟨1 / 2, by norm_num, hW.a_half⟩ hR hEF hρ₀ hE
    (frobSq_Ppart_le ppInput_of_PP hMV hC _ _ ⟨h0, h1.le⟩)

/-- P1 for Z′, quartic window. -/
theorem coeffMoments_quartic_w (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ)
    {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) (hF : wCoeffFamily.Hyps) :
    CoeffMoments Z ((paramsOf ϱ lam).atV vQuartic) wCoeffFamily (kappaXi lam vQuartic) :=
  coeffMoments_quartic_D1 Z hR hϱ h0 h1 hF rfl

/-- **P2 for Z′ (W), quartic family.** -/
theorem traceTransfer_quartic_w (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) {ϱ : ℝ → ℝ}
    (hϱ : TaperProfile ϱ) {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1)
    (hEF : WEF Z ((paramsOf ϱ lam).atV vQuartic)) :
    XiTraceTransfer Z ((paramsOf ϱ lam).atV vQuartic) wCoeffFamily := by
  have hP := paramsOf_valid hϱ h0 h1.le
  obtain ⟨C, hC, hMV⟩ := MV.mv_hilbert
  obtain ⟨e, ρ₀, A, T₁, hρ₀, hE⟩ := wReexpansion
  have hW := windowZeroSide_atV Z hR hP
  have hcore : ∃ T₁ : ℝ, ∀ T : ℝ, T₁ ≤ T → PrimeSide.LocalHypsCore (cQ (paramsOf ϱ lam).ϱ)
      (((paramsOf ϱ lam).atV vQuartic T).toSetting T) (((paramsOf ϱ lam).atV vQuartic T).localFun T) := by
    obtain ⟨T₁, hT₁⟩ := localHypsCoreQ_eventually hP
    refine ⟨T₁, fun T hT => ?_⟩
    rw [Params.atV_toSetting, Params.atV_localFun T hP vQuartic_even]
    exact hT₁ T hT
  exact wTraceTransfer_of Z _ wCoeffFamily (paramsOf ϱ lam) hP h1 (fun _ => ⟨rfl, rfl⟩) hcore gammaFacts
    ⟨1 / 2, by norm_num, hW.a_half⟩ hR hEF hρ₀ hE
    (frobSq_Ppart_le ppInput_of_PP hMV hC _ _ ⟨h0, h1.le⟩)

end XiPrime
end Zeta23

end
