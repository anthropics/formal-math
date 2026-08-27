/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmE/Main.lean — Theorem E: [thm:E]'s bounds at fixed λ modulo the
χ-traces package and the χ-EF bridge.

Mirror of Zeta23/Main.lean's thm{A,B,C}_lam_of_traces for a primitive Dirichlet character: the
zero-side/tail/taper inputs are discharged from the SAME Z-generic project files
(ZeroSide, Tail, Taper — nothing ζ-specific in them), while the two genuinely
χ-arithmetic inputs stay explicit named hypotheses:
  hTr   — [thm:traces] for ν_{X,χ} (ThmTracesHypChi),
  hGzGp — the [eq:Gdef]-identity for L(s,χ) (zero side = prime side, from H-EF(χ)).
-/
import Zeta23.ThmE.Statement
import Zeta23.ThmE.AssemblyQ
import Zeta23.ThmE.SeamL
import Zeta23.ThmE.GzGpChi
import Zeta23.ThmE.RvMChi
import Zeta23.ThmE.TracesChi
import Zeta23.ThmE.ChebCoprime
import Zeta23.ThmE.GammaFactsChiProof
import Zeta23.MV.Final
import Zeta23.PrimeSideA.Bridge
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Zeta23.Main

open Filter Topology

noncomputable section

namespace Zeta23
namespace ThmE

/-- [prop:tail] package for a χ-configuration (mirror of `Tail.eventually_tailPackage`, whose only
use of `PaperInputs` is the local count — here taken from `RiemannVonMangoldtChi`). -/
theorem tailPackageChi (Z : ZeroConfig) {q : ℕ} (hRvM : RiemannVonMangoldtChi q Z)
    (P : Params) (hP : P.Valid) :
    ∃ θ₀ : ℝ → ℝ, (∀ᶠ T in atTop, Assembly.TailInputs Z P T (θ₀ T)) ∧
      ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1) := by
  obtain ⟨A₀, hA₀, hloc⟩ := hRvM.local_count
  have hwL : ∀ᶠ T in atTop, 8 * P.w ≤ P.L T := (Tail.tendsto_L_atTop P hP).eventually_ge_atTop _
  refine ⟨fun T => Tail.theta0 A₀ (Real.exp (P.L T / 4) * P.C1 T) T, ?_, ?_⟩
  · refine Tail.eventually_tailInputs Z P hP hA₀ hloc (fun T => P.C1 T)
      (fun T => Tail.C1_nonneg P T) ?_ ?_ ?_
    · filter_upwards [hwL] with T hwL
      exact fun r y hy hz => Params.norm_phiHat_sub_I_mul_le hP hwL r y hy hz
    · filter_upwards [hwL] with T hwL
      linarith [Params.half_le_a hP hwL]
    · exact Eventually.of_forall fun T z => GzGp.phiHat_conj P T z
  · exact Tail.eventually_theta0_le P hP hA₀ (fun T => P.C1 T) (fun T => Tail.C1_nonneg P T)
      (hwL.mono fun T hwL => Params.C1_le hP hwL)

/-- boundary count for a χ-configuration (from the two-sided local count). -/
theorem NIIChi (Z : ZeroConfig) {q : ℕ} (hRvM : RiemannVonMangoldtChi q Z) :
    ∃ C : ℝ, ∀ᶠ T in atTop, (Assembly.NII Z T : ℝ) ≤ C * Real.sqrt T * l T := by
  obtain ⟨A₀, hA₀, hloc⟩ := hRvM.local_count
  exact Tail.eventually_NII_le Z hA₀ hloc

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- **Theorem E, first bound, at fixed λ ∈ (0,1), modulo the χ-traces package and the χ-EF
bridge** ([thm:E]; the analogue of Zeta23.thmA_lam_of_traces). -/
theorem thmE_A_lam_of_traces (hs : LSeam χ) (hq : 1 ≤ q)
    {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ) {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1)
    (hRvM : RiemannVonMangoldtChi q (LZeros hs))
    (hTr : ThmTracesHypChi (paramsOf ϱ lam) (parity χ) q (coeff χ) (LZeros hs))
    (hGzGp : ∀ᶠ T in atTop,
      (LZeros hs).Gz (paramsOf ϱ lam) T = GpChi (paramsOf ϱ lam) (parity χ) q (coeff χ) T)
    (hcalE : Tendsto (paramsOf ϱ lam).calE atTop (𝓝 0)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Hfun lam - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0starL χ T (2 * T) := by
  have hP := paramsOf_valid hϱ h0 h1.le
  obtain ⟨θ₀, hTail, hθ₀⟩ := tailPackageChi (LZeros hs) hRvM _ hP
  have hBlock := eventually_blockInputs (LZeros hs) _ hP
  have hNII := NIIChi (LZeros hs) hRvM
  have ha : ∀ᶠ T in atTop,
      1 - 2 * (paramsOf ϱ lam).w / (paramsOf ϱ lam).L T ≤ (paramsOf ϱ lam).a T ∧
        (paramsOf ϱ lam).a T ≤ 1 := by
    have hwL : ∀ᶠ T in atTop, 8 * (paramsOf ϱ lam).w ≤ (paramsOf ϱ lam).L T :=
      (Tail.tendsto_L_atTop _ hP).eventually_ge_atTop _
    filter_upwards [hwL] with T hwL
    exact ⟨(Params.one_sub_le_b hP hwL).trans (Params.b_le_a hP hwL), Params.a_le_one hP hwL⟩
  have h := thmE_A_abstract (LZeros hs) (parity χ) hq (coeff χ) (paramsOf ϱ lam) hP h1
    hRvM hTr hBlock θ₀ hTail hθ₀ hNII hGzGp ha hcalE
  simpa [paramsOf] using h

/-- **Theorem E, second bound (simple on-line zeros) at fixed λ, modulo the χ inputs** ([thm:E]). -/
theorem thmE_B_lam_of_traces (hs : LSeam χ) (hq : 1 ≤ q)
    {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ) {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1)
    (hRvM : RiemannVonMangoldtChi q (LZeros hs))
    (hTr : ThmTracesHypChi (paramsOf ϱ lam) (parity χ) q (coeff χ) (LZeros hs))
    (hGzGp : ∀ᶠ T in atTop,
      (LZeros hs).Gz (paramsOf ϱ lam) T = GpChi (paramsOf ϱ lam) (parity χ) q (coeff χ) T)
    (hcalE : Tendsto (paramsOf ϱ lam).calE atTop (𝓝 0)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 * Ffun lam - 1 - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0simpleL χ T (2 * T) := by
  have hP := paramsOf_valid hϱ h0 h1.le
  obtain ⟨θ₀, hTail, hθ₀⟩ := tailPackageChi (LZeros hs) hRvM _ hP
  have hBlock := eventually_blockInputs (LZeros hs) _ hP
  have hNII := NIIChi (LZeros hs) hRvM
  obtain ⟨R, hR, hev⟩ := thmE_BC_core (LZeros hs) (parity χ) hq (coeff χ) (paramsOf ϱ lam) hP h1
    hRvM hTr hBlock θ₀ hTail hθ₀ hNII hGzGp hcalE
  have h := Assembly.eps_form_of_isLittleO (err := fun T => 2 * R T) (hev.mono fun T h => by
      simpa using h.1)
    (Filter.Eventually.of_forall fun T => Nat.cast_nonneg _) (hR.const_mul_left 2)
  simpa [paramsOf] using h

/-- **Theorem E, third bound (distinct zeros) at fixed λ, modulo the χ inputs** ([thm:E]). -/
theorem thmE_C_lam_of_traces (hs : LSeam χ) (hq : 1 ≤ q)
    {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ) {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1)
    (hRvM : RiemannVonMangoldtChi q (LZeros hs))
    (hTr : ThmTracesHypChi (paramsOf ϱ lam) (parity χ) q (coeff χ) (LZeros hs))
    (hGzGp : ∀ᶠ T in atTop,
      (LZeros hs).Gz (paramsOf ϱ lam) T = GpChi (paramsOf ϱ lam) (parity χ) q (coeff χ) T)
    (hcalE : Tendsto (paramsOf ϱ lam).calE atTop (𝓝 0)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Ffun lam - ε) * (NcountL χ T (2 * T) : ℝ) ≤ NdistL χ T (2 * T) := by
  have hP := paramsOf_valid hϱ h0 h1.le
  obtain ⟨θ₀, hTail, hθ₀⟩ := tailPackageChi (LZeros hs) hRvM _ hP
  have hBlock := eventually_blockInputs (LZeros hs) _ hP
  have hNII := NIIChi (LZeros hs) hRvM
  obtain ⟨R, hR, hev⟩ := thmE_BC_core (LZeros hs) (parity χ) hq (coeff χ) (paramsOf ϱ lam) hP h1
    hRvM hTr hBlock θ₀ hTail hθ₀ hNII hGzGp hcalE
  have h := Assembly.eps_form_of_isLittleO (err := R) (hev.mono fun T h => by simpa using h.2)
    (Filter.Eventually.of_forall fun T => Nat.cast_nonneg _) hR
  simpa [paramsOf] using h

/-! ## The seam discharged (Zeta23/ThmE/SeamL.lean): the gates without the `LSeam` hypothesis -/

section SeamDischarged

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- Theorem E bound 1 at fixed λ, for a PRIMITIVE χ mod q > 1;
remaining hypotheses: RvM(χ), the χ-traces package, the χ-EF bridge, 𝓔 → 0. -/
theorem thmE_A_lam_of_traces' (hq : 1 < q) (hprim : χ.IsPrimitive)
    {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ) {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1)
    (hRvM : RiemannVonMangoldtChi q (LZeros (LSeam_of hq hprim)))
    (hTr : ThmTracesHypChi (paramsOf ϱ lam) (parity χ) q (coeff χ) (LZeros (LSeam_of hq hprim)))
    (hGzGp : ∀ᶠ T in Filter.atTop,
      (LZeros (LSeam_of hq hprim)).Gz (paramsOf ϱ lam) T
        = GpChi (paramsOf ϱ lam) (parity χ) q (coeff χ) T)
    (hcalE : Filter.Tendsto (paramsOf ϱ lam).calE Filter.atTop (nhds 0)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Hfun lam - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0starL χ T (2 * T) :=
  thmE_A_lam_of_traces (LSeam_of hq hprim) (by omega) hϱ h0 h1 hRvM hTr hGzGp hcalE

/-- Theorem E bound 2, seam discharged. -/
theorem thmE_B_lam_of_traces' (hq : 1 < q) (hprim : χ.IsPrimitive)
    {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ) {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1)
    (hRvM : RiemannVonMangoldtChi q (LZeros (LSeam_of hq hprim)))
    (hTr : ThmTracesHypChi (paramsOf ϱ lam) (parity χ) q (coeff χ) (LZeros (LSeam_of hq hprim)))
    (hGzGp : ∀ᶠ T in Filter.atTop,
      (LZeros (LSeam_of hq hprim)).Gz (paramsOf ϱ lam) T
        = GpChi (paramsOf ϱ lam) (parity χ) q (coeff χ) T)
    (hcalE : Filter.Tendsto (paramsOf ϱ lam).calE Filter.atTop (nhds 0)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 * Ffun lam - 1 - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0simpleL χ T (2 * T) :=
  thmE_B_lam_of_traces (LSeam_of hq hprim) (by omega) hϱ h0 h1 hRvM hTr hGzGp hcalE

/-- Theorem E bound 3, seam discharged. -/
theorem thmE_C_lam_of_traces' (hq : 1 < q) (hprim : χ.IsPrimitive)
    {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ) {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1)
    (hRvM : RiemannVonMangoldtChi q (LZeros (LSeam_of hq hprim)))
    (hTr : ThmTracesHypChi (paramsOf ϱ lam) (parity χ) q (coeff χ) (LZeros (LSeam_of hq hprim)))
    (hGzGp : ∀ᶠ T in Filter.atTop,
      (LZeros (LSeam_of hq hprim)).Gz (paramsOf ϱ lam) T
        = GpChi (paramsOf ϱ lam) (parity χ) q (coeff χ) T)
    (hcalE : Filter.Tendsto (paramsOf ϱ lam).calE Filter.atTop (nhds 0)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Ffun lam - ε) * (NcountL χ T (2 * T) : ℝ) ≤ NdistL χ T (2 * T) :=
  thmE_C_lam_of_traces (LSeam_of hq hprim) (by omega) hϱ h0 h1 hRvM hTr hGzGp hcalE

omit [NeZero q] in
/-- the χ-EF bridge at FIXED T (the eventual form below is this plus
two asymptotic side conditions). Conditions: 0 < L(T) and 8w ≤ L(T). -/
theorem GzGpChi_at {Z : ZeroConfig} {κ : ℕ} {c : ℕ → ℂ} (P : Params) (hP : P.Valid)
    (hEF : ExplicitFormulaPaperChi κ q c Z) (T : ℝ)
    (hL : 0 < P.L T) (hwL : 8 * P.w ≤ P.L T) :
    Z.Gz P T = GpChi P κ q c T := by
  refine Z.Gz_eq_GpChi P κ q c T hEF hL ?_ ?_
  · exact (Complex.ofRealCLM.contDiff.comp (Params.phi_contDiff hP hwL)).of_le (by norm_num)
  · exact closure_minimal (Params.phi_support_subset hP) isClosed_Icc

/-- the χ-EF bridge, eventual-in-T form (`Gz_eq_GpChi` + the Taper side conditions;
mirror of Main.lean's `eventually_side_conditions` first component). -/
theorem eventually_GzGpChi {Z : ZeroConfig} {κ : ℕ} {c : ℕ → ℂ} (P : Params) (hP : P.Valid)
    (hEF : ExplicitFormulaPaperChi κ q c Z) :
    ∀ᶠ T in Filter.atTop, Z.Gz P T = GpChi P κ q c T := by
  have hLtop := Assembly.tendsto_L_atTop P hP.lam_pos
  have hwL : ∀ᶠ T in Filter.atTop, 8 * P.w ≤ P.L T := hLtop.eventually_ge_atTop _
  have hLpos : ∀ᶠ T in Filter.atTop, 0 < P.L T := hLtop.eventually_gt_atTop _
  filter_upwards [hwL, hLpos] with T hwL hL
  exact GzGpChi_at P hP hEF T hL hwL

/-- **Theorem E bound 1 at fixed λ**: remaining inputs are
exactly the χ-arithmetic trio (EF(χ) paper form, RvM(χ), traces(χ)). -/
theorem thmE_A_lam_final (hq : 1 < q) (hprim : χ.IsPrimitive)
    {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ) {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1)
    (hEF : ExplicitFormulaPaperChi (parity χ) q (coeff χ) (LZeros (LSeam_of hq hprim)))
    (hRvM : RiemannVonMangoldtChi q (LZeros (LSeam_of hq hprim)))
    (hTr : ThmTracesHypChi (paramsOf ϱ lam) (parity χ) q (coeff χ) (LZeros (LSeam_of hq hprim))) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Hfun lam - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0starL χ T (2 * T) := by
  have hP := paramsOf_valid hϱ h0 h1.le
  exact thmE_A_lam_of_traces' hq hprim hϱ h0 h1 hRvM hTr
    (eventually_GzGpChi _ hP hEF)
    (Assembly.calE_tendsto_zero _ hP.lam_pos hP.lam_le_one (zero_le_one.trans hP.one_le_w))

/-- same, bound 2 (simple on-line). -/
theorem thmE_B_lam_final (hq : 1 < q) (hprim : χ.IsPrimitive)
    {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ) {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1)
    (hEF : ExplicitFormulaPaperChi (parity χ) q (coeff χ) (LZeros (LSeam_of hq hprim)))
    (hRvM : RiemannVonMangoldtChi q (LZeros (LSeam_of hq hprim)))
    (hTr : ThmTracesHypChi (paramsOf ϱ lam) (parity χ) q (coeff χ) (LZeros (LSeam_of hq hprim))) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 * Ffun lam - 1 - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0simpleL χ T (2 * T) := by
  have hP := paramsOf_valid hϱ h0 h1.le
  exact thmE_B_lam_of_traces' hq hprim hϱ h0 h1 hRvM hTr
    (eventually_GzGpChi _ hP hEF)
    (Assembly.calE_tendsto_zero _ hP.lam_pos hP.lam_le_one (zero_le_one.trans hP.one_le_w))

/-- same, bound 3 (distinct). -/
theorem thmE_C_lam_final (hq : 1 < q) (hprim : χ.IsPrimitive)
    {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ) {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1)
    (hEF : ExplicitFormulaPaperChi (parity χ) q (coeff χ) (LZeros (LSeam_of hq hprim)))
    (hRvM : RiemannVonMangoldtChi q (LZeros (LSeam_of hq hprim)))
    (hTr : ThmTracesHypChi (paramsOf ϱ lam) (parity χ) q (coeff χ) (LZeros (LSeam_of hq hprim))) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Ffun lam - ε) * (NcountL χ T (2 * T) : ℝ) ≤ NdistL χ T (2 * T) := by
  have hP := paramsOf_valid hϱ h0 h1.le
  exact thmE_C_lam_of_traces' hq hprim hϱ h0 h1 hRvM hTr
    (eventually_GzGpChi _ hP hEF)
    (Assembly.calE_tendsto_zero _ hP.lam_pos hP.lam_le_one (zero_le_one.trans hP.one_le_w))

/-! ## RvM(χ) discharged (Zeta23.ThmE.rvmChi): remaining inputs are
(EF(χ) paper form, traces(χ)). -/

/-- **Theorem E bound 1 at fixed λ, TWO hypotheses** (EF-bridge side conditions, 𝓔 → 0 and
RvM(χ) all discharged). -/
theorem thmE_A_lam₂ (hq : 1 < q) (hprim : χ.IsPrimitive)
    {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ) {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1)
    (hEF : ExplicitFormulaPaperChi (parity χ) q (coeff χ) (LZeros (LSeam_of hq hprim)))
    (hTr : ThmTracesHypChi (paramsOf ϱ lam) (parity χ) q (coeff χ) (LZeros (LSeam_of hq hprim))) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Hfun lam - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0starL χ T (2 * T) :=
  thmE_A_lam_final hq hprim hϱ h0 h1 hEF (rvmChi hq hprim) hTr

/-- bound 2, two hypotheses. -/
theorem thmE_B_lam₂ (hq : 1 < q) (hprim : χ.IsPrimitive)
    {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ) {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1)
    (hEF : ExplicitFormulaPaperChi (parity χ) q (coeff χ) (LZeros (LSeam_of hq hprim)))
    (hTr : ThmTracesHypChi (paramsOf ϱ lam) (parity χ) q (coeff χ) (LZeros (LSeam_of hq hprim))) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 * Ffun lam - 1 - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0simpleL χ T (2 * T) :=
  thmE_B_lam_final hq hprim hϱ h0 h1 hEF (rvmChi hq hprim) hTr

/-- bound 3, two hypotheses. -/
theorem thmE_C_lam₂ (hq : 1 < q) (hprim : χ.IsPrimitive)
    {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ) {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1)
    (hEF : ExplicitFormulaPaperChi (parity χ) q (coeff χ) (LZeros (LSeam_of hq hprim)))
    (hTr : ThmTracesHypChi (paramsOf ϱ lam) (parity χ) q (coeff χ) (LZeros (LSeam_of hq hprim))) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Ffun lam - ε) * (NcountL χ T (2 * T) : ℝ) ≤ NdistL χ T (2 * T) :=
  thmE_C_lam_final hq hprim hϱ h0 h1 hEF (rvmChi hq hprim) hTr

end SeamDischarged

/-! ## thm:traces(χ) discharged via `thm_traces_chi`: Theorem E at ONE hypothesis -/

section OneHyp

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

omit [NeZero q] in
/-- the coefficient sequence of a primitive character is unimodular-on-coprime
(values of norm ≤ 1 everywhere, = 1 on units, 0 off units; Mathlib's
`DirichletCharacter.norm_le_one` / `unit_norm_eq_one` / `MulChar.map_nonunit` +
`ZMod.isUnit_iff_coprime`). -/
lemma coeffUnimodular_of_primitive (_hq : 1 < q) (_hprim : χ.IsPrimitive) :
    CoeffUnimodular q (coeff χ) where
  norm_le := fun n => χ.norm_le_one _
  vanish := fun n hn => by
    have : ¬ IsUnit ((n : ZMod q)) := by
      rwa [ZMod.isUnit_iff_coprime]
    exact χ.map_nonunit this
  norm_eq := fun n _ hn => by
    have hu : IsUnit ((n : ZMod q)) := by
      rwa [ZMod.isUnit_iff_coprime]
    simpa [coeff] using χ.unit_norm_eq_one hu.unit

omit [NeZero q] in
/-- parity is ≤ 1 by construction. -/
lemma parity_le_one : parity χ ≤ 1 := by
  unfold parity
  split <;> omega

/-- **PaperInputsChi from the χ-EF alone**: every other field is a theorem
(rvmChi, chebyshevMertens, chebyshevMertensCoprime, mvDiag_thirteen, gammaFactsChi). -/
theorem PaperInputsChi.of_EF (hq : 1 < q) (hprim : χ.IsPrimitive)
    (hEF : ExplicitFormulaPaperChi (parity χ) q (coeff χ) (LZeros (LSeam_of hq hprim))) :
    PaperInputsChi (parity χ) q (coeff χ) (LZeros (LSeam_of hq hprim)) where
  EF := hEF
  RvM := rvmChi hq hprim
  cheb := Cheb.chebyshevMertens
  chebq := chebyshevMertensCoprime q (by omega)
  MV := exists_MVHilbert_of_diag ⟨13, by norm_num, MV.mvDiag_thirteen⟩
  Gamma := GammaChi.gammaFactsChi parity_le_one (by omega)

/-- **Theorem E bound 1 at fixed λ, ONE hypothesis** — everything but the χ-explicit formula
(paper form) is a theorem. -/
theorem thmE_A_lam₁ (hq : 1 < q) (hprim : χ.IsPrimitive)
    {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1)
    (hEF : ExplicitFormulaPaperChi (parity χ) q (coeff χ) (LZeros (LSeam_of hq hprim))) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Hfun lam - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0starL χ T (2 * T) := by
  have hP := paramsOf_valid taperProfile_stdProfile h0 h1.le
  exact thmE_A_lam₂ hq hprim taperProfile_stdProfile h0 h1 hEF
    (thm_traces_chi hP (by omega) (coeffUnimodular_of_primitive hq hprim)
      (PaperInputsChi.of_EF hq hprim hEF) (PrimeSide.localHypsEventually hP))

/-- bound 2, one hypothesis. -/
theorem thmE_B_lam₁ (hq : 1 < q) (hprim : χ.IsPrimitive)
    {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1)
    (hEF : ExplicitFormulaPaperChi (parity χ) q (coeff χ) (LZeros (LSeam_of hq hprim))) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 * Ffun lam - 1 - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0simpleL χ T (2 * T) := by
  have hP := paramsOf_valid taperProfile_stdProfile h0 h1.le
  exact thmE_B_lam₂ hq hprim taperProfile_stdProfile h0 h1 hEF
    (thm_traces_chi hP (by omega) (coeffUnimodular_of_primitive hq hprim)
      (PaperInputsChi.of_EF hq hprim hEF) (PrimeSide.localHypsEventually hP))

/-- bound 3, one hypothesis. -/
theorem thmE_C_lam₁ (hq : 1 < q) (hprim : χ.IsPrimitive)
    {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1)
    (hEF : ExplicitFormulaPaperChi (parity χ) q (coeff χ) (LZeros (LSeam_of hq hprim))) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Ffun lam - ε) * (NcountL χ T (2 * T) : ℝ) ≤ NdistL χ T (2 * T) := by
  have hP := paramsOf_valid taperProfile_stdProfile h0 h1.le
  exact thmE_C_lam₂ hq hprim taperProfile_stdProfile h0 h1 hEF
    (thm_traces_chi hP (by omega) (coeffUnimodular_of_primitive hq hprim)
      (PaperInputsChi.of_EF hq hprim hEF) (PrimeSide.localHypsEventually hP))

end OneHyp

end ThmE
end Zeta23
