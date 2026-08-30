/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization.

Zeta23/XiPrime/PrimeSide/Moments.lean — ξ′ generalised-coefficient prime side: the
Params-level hat-unit bridge to Statement.lean's 'CoeffMoments'.

CoeffMoments Z Pf F κ: for every δ > 0, eventually
  (1−δ)N ≤ tr M̂ᵀ ≤ (1+δ)N  and  ‖M̂ᵀ‖²_F ≤ (κ+δ)N,
with M̂ᵀ = (Pf T).hat T ((Pf T).GpC T (F.c T)), N = N(T,2T) of Z.  Here: tr M̂ᵀ = tr G̃/(aL) and
‖M̂ᵀ‖²_F = tr G̃²/(aL)² (Zeta23/Assembly Part D, verbatim for the general-coefficient matrix), so the
package TracesBoundsXi of the concrete data (Concrete.lean) plus the window limit
cRatio(λ₁; a_T, b_T, J_T) → c∞ > 0 (XiPrime/Window.lean) give CoeffMoments with
κ = c∞⁻¹.  Stated once for any height-indexed family Pf whose scalars are P's and whose taper data
are those of the window (Pf T).phi T — both 'fun _ => P' (flat) and 'P.atV v' (profile v)
satisfy the three bookkeeping identities by rfl.
-/
import Zeta23.XiPrime.PrimeSide.Concrete
import Zeta23.PrimeSideB.Traces
import Zeta23.Assembly

noncomputable section

open Real Filter Topology MeasureTheory
open scoped BigOperators

namespace Zeta23
namespace XiPrime

open PrimeSide PaperParams RHLinalg Assembly

/-! ## Entrywise identification of the statement-layer matrices with the abstract-layer traces -/

section Units
variable (Q : Params) (T : ℝ)

/-- The fixed-coefficient prime-side matrix with pole weight `cΠ` (`GpC` is the case `cΠ = 1` by rfl;
the Z′ layer uses `cΠ = 2`). -/
def _root_.Zeta23.Params.GpCW (cPi : ℝ) (c : ℕ → ℂ) : Matrix (Fin (Q.d T)) (Fin (Q.d T)) ℂ :=
  fun k l => (Q.GentryCW T cPi c (k : ℤ) (l : ℤ) : ℂ)

lemma GpC_eq_GpCW (c : ℕ → ℂ) : Q.GpC T c = Q.GpCW T 1 c := rfl

lemma GentryCW_eq (cPi : ℝ) (c : ℕ → ℂ) (k l : ℤ) :
    Q.GentryCW T cPi c k l = GentryW cPi c (Q.toSetting T) (Q.localFun T) k l := rfl

/-- `tr M̃ᵀ` computed entrywise. -/
lemma rtrace_tilde_GpCW (cPi : ℝ) (c : ℕ → ℂ) :
    rtrace (Q.tilde T (Q.GpCW T cPi c)) = trGtW cPi c (Q.toSetting T) (Q.localFun T) := by
  rw [tilde_eq, rtrace_smul_ofReal]
  simp [trGtW, rtrace, Matrix.trace, Params.GpCW, GentryCW_eq]
  left; rfl

/-- `‖M̃ᵀ‖²_F` computed entrywise. -/
lemma frobSq_tilde_GpCW (cPi : ℝ) (c : ℕ → ℂ) :
    frobSq (Q.tilde T (Q.GpCW T cPi c)) = trGt2W cPi c (Q.toSetting T) (Q.localFun T) := by
  rw [tilde_eq, frobSq_smul_ofReal, frobSq_eq_sum_norm_sq]
  simp [trGt2W, Params.GpCW, GentryCW_eq, sq_abs]
  left; rfl

lemma rtrace_hat_GpCW (cPi : ℝ) (c : ℕ → ℂ) :
    rtrace (Q.hat T (Q.GpCW T cPi c))
      = trGtW cPi c (Q.toSetting T) (Q.localFun T) / (Q.a T * Q.L T) := by
  rw [rtrace_hat, rtrace_tilde_GpCW, div_eq_inv_mul]

lemma frobSq_hat_GpCW (cPi : ℝ) (c : ℕ → ℂ) :
    frobSq (Q.hat T (Q.GpCW T cPi c))
      = trGt2W cPi c (Q.toSetting T) (Q.localFun T) / (Q.a T * Q.L T) ^ 2 := by
  rw [frobSq_hat, frobSq_tilde_GpCW, div_eq_inv_mul, inv_pow]

end Units

/-- the CoeffMoments sentence with a general pole weight (`CoeffMoments Z Pf F κ` is the case
`cΠ = 1`, by rfl): for every δ > 0, eventually `(1−δ)N ≤ tr M̂ ≤ (1+δ)N` and `‖M̂‖²_F ≤ (κ+δ)N`. -/
def MomentsW (Z : ZeroConfig) (Pf : ℝ → Params) (F : CoeffFamily) (cPi κ : ℝ) : Prop :=
  (∀ δ : ℝ, 0 < δ → ∀ᶠ T in atTop,
    (1 - δ) * (Z.N T (2 * T) : ℝ) ≤ rtrace ((Pf T).hat T ((Pf T).GpCW T cPi (F.c T))) ∧
    rtrace ((Pf T).hat T ((Pf T).GpCW T cPi (F.c T))) ≤ (1 + δ) * (Z.N T (2 * T) : ℝ)) ∧
  (∀ δ : ℝ, 0 < δ → ∀ᶠ T in atTop,
    frobSq ((Pf T).hat T ((Pf T).GpCW T cPi (F.c T))) ≤ (κ + δ) * (Z.N T (2 * T) : ℝ))

lemma coeffMoments_iff_momentsW (Z : ZeroConfig) (Pf : ℝ → Params) (F : CoeffFamily) (κ : ℝ) :
    CoeffMoments Z Pf F κ ↔ MomentsW Z Pf F 1 κ := Iff.rfl

/-! ## CoeffMoments from the trace package and the window limit -/

/-- **CoeffMoments for a height-indexed parameter family** whose scalars are `P`'s and whose taper
data at height `T` are those of the window `(Pf T).phi T` (the three identities hold by `rfl` for
`Pf := fun _ => P` and for `Pf := P.atV v`).  Inputs: P.Valid, λ < 1, the window family is admissible
(Zeta23.AdmWindow, b ≥ 1/2) eventually, CoeffFamily.Hyps, H-Γ, H-MV, [prop:PP] for P_c (PPInput),
H-RvM for `Z`, and the window limit `cRatio(λ₁; a_T, b_T, J_T) → c∞ > 0`.  Output: `CoeffMoments Z Pf Fam c∞⁻¹`. -/
theorem momentsW_of_family {P : Params} {Pf : ℝ → Params} {Fam : CoeffFamily} {cW : ℝ}
    {Z : ZeroConfig} (cPi : ℝ) (hP : P.Valid) (hlam1 : P.lam < 1)
    (hset : ∀ T, (Pf T).toSetting T = P.toSetting T)
    (hloc : ∀ T, (Pf T).localFun T = AdmWindow.localFun ((Pf T).phi T) (P.L T))
    (haL : ∀ T, (Pf T).a T * (Pf T).L T = AdmWindow.av ((Pf T).phi T) (P.L T) * P.L T)
    (hwin : AdmFamily P (fun T => (Pf T).phi T) cW)
    (hF : Fam.Hyps) (hΓ : Zeta23.GammaFacts) (hMV : ∃ C : ℝ, 0 < C ∧ Zeta23.MVHilbert C)
    (hPP : PPInput) (hRvM : RiemannVonMangoldt Z) {cinf : ℝ} (hc0 : 0 < cinf)
    (hc : Tendsto (fun T => ThmD.cRatio (P.lam1 T) (AdmWindow.av ((Pf T).phi T) (P.L T))
        (AdmWindow.bv ((Pf T).phi T) (P.L T))
        (JD Fam.D (AdmWindow.gv ((Pf T).phi T)) (P.L T) (l T))) atTop (𝓝 cinf)) :
    MomentsW Z Pf Fam cPi cinf⁻¹ := by
  set win : ℝ → ℝ → ℝ := fun T => (Pf T).phi T with hwin_def
  set Ncnt : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hN_def
  have hN := rvm_evBound hRvM
  have hTr := tracesBoundsXi_concrete (P := P) (win := win) (Fam := Fam) (cPi := cPi) (cW := cW)
    (Ncnt := Ncnt) hP hlam1 hwin hF hΓ hMV hPP hN
  have hN0 : ∀ᶠ T in atTop, 0 ≤ Ncnt T := Eventually.of_forall fun T => Nat.cast_nonneg _
  obtain ⟨Tw, hTw⟩ := id hwin
  have haLne : ∀ᶠ T in atTop, AdmWindow.av (win T) (P.L T) * P.L T ≠ 0 := by
    filter_upwards [eventually_ge_atTop Tw, eventually_L_ge P hP.lam_pos 1] with T hT hL
    obtain ⟨hW, hb⟩ := hTw T hT
    have ha : 1 / 2 ≤ AdmWindow.av (win T) (P.L T) := hb.trans hW.bv_le_av
    exact mul_ne_zero (by linarith) (by linarith)
  -- rewrite the statement's hat-unit quantities into the concrete data
  have htr_eq : ∀ T, rtrace ((Pf T).hat T ((Pf T).GpCW T cPi (Fam.c T)))
      = (concreteData P win Fam cPi Ncnt).trG T
          / ((concreteData P win Fam cPi Ncnt).aT T * P.L T) := by
    intro T
    rw [rtrace_hat_GpCW, haL, hset, hloc]
    rfl
  have hfr_eq : ∀ T, frobSq ((Pf T).hat T ((Pf T).GpCW T cPi (Fam.c T)))
      = (concreteData P win Fam cPi Ncnt).trG2 T
          / ((concreteData P win Fam cPi Ncnt).aT T * P.L T) ^ 2 := by
    intro T
    rw [frobSq_hat_GpCW, haL, hset, hloc]
    rfl
  refine ⟨fun δ hδ => ?_, fun δ hδ => ?_⟩
  · filter_upwards [moments_trace hTr hN0 haLne hδ] with T hT
    rw [htr_eq]
    exact hT
  · filter_upwards [moments_frob hTr hN0 hc0 hc hδ] with T hT
    rw [hfr_eq]
    exact hT

/-- **CoeffMoments (pole weight 1) for a height-indexed parameter family** — the statement as a `Prop`. -/
theorem coeffMoments_of_family {P : Params} {Pf : ℝ → Params} {Fam : CoeffFamily} {cW : ℝ}
    {Z : ZeroConfig} (hP : P.Valid) (hlam1 : P.lam < 1)
    (hset : ∀ T, (Pf T).toSetting T = P.toSetting T)
    (hloc : ∀ T, (Pf T).localFun T = AdmWindow.localFun ((Pf T).phi T) (P.L T))
    (haL : ∀ T, (Pf T).a T * (Pf T).L T = AdmWindow.av ((Pf T).phi T) (P.L T) * P.L T)
    (hwin : AdmFamily P (fun T => (Pf T).phi T) cW)
    (hF : Fam.Hyps) (hΓ : Zeta23.GammaFacts) (hMV : ∃ C : ℝ, 0 < C ∧ Zeta23.MVHilbert C)
    (hPP : PPInput) (hRvM : RiemannVonMangoldt Z) {cinf : ℝ} (hc0 : 0 < cinf)
    (hc : Tendsto (fun T => ThmD.cRatio (P.lam1 T) (AdmWindow.av ((Pf T).phi T) (P.L T))
        (AdmWindow.bv ((Pf T).phi T) (P.L T))
        (JD Fam.D (AdmWindow.gv ((Pf T).phi T)) (P.L T) (l T))) atTop (𝓝 cinf)) :
    CoeffMoments Z Pf Fam cinf⁻¹ :=
  (coeffMoments_iff_momentsW Z Pf Fam _).2
    (momentsW_of_family 1 hP hlam1 hset hloc haL hwin hF hΓ hMV hPP hRvM hc0 hc)

/-- **CoeffMoments, flat window** (`Pf := fun _ => P`; the window is the tree's own taper `P.phi T`,
admissible with constant `cW` — XiPrime/Window.lean's admWindow_taper gives `cW = P.crho`). -/
theorem coeffMoments_flat {P : Params} {Fam : CoeffFamily} {cW : ℝ} {Z : ZeroConfig}
    (hP : P.Valid) (hlam1 : P.lam < 1)
    (hwin : AdmFamily P (fun T => P.phi T) cW)
    (hF : Fam.Hyps) (hΓ : Zeta23.GammaFacts) (hMV : ∃ C : ℝ, 0 < C ∧ Zeta23.MVHilbert C)
    (hPP : PPInput) (hRvM : RiemannVonMangoldt Z) {cinf : ℝ} (hc0 : 0 < cinf)
    (hc : Tendsto (fun T => ThmD.cRatio (P.lam1 T) (P.a T) (P.b T)
        (JD Fam.D (P.g T) (P.L T) (l T))) atTop (𝓝 cinf)) :
    CoeffMoments Z (fun _ => P) Fam cinf⁻¹ :=
  coeffMoments_of_family (Pf := fun _ => P) hP hlam1 (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    hwin hF hΓ hMV hPP hRvM hc0 hc

/-- **CoeffMoments, window profile v** (`Pf := P.atV v`; the window at height T is `(P.atV v T).phi T`,
whose eventual admissibility is the hypothesis `hwin`). -/
theorem coeffMoments_atV {P : Params} {v : ℝ → ℝ} {Fam : CoeffFamily} {cW : ℝ} {Z : ZeroConfig}
    (hP : P.Valid) (hlam1 : P.lam < 1)
    (hwin : AdmFamily P (fun T => (P.atV v T).phi T) cW)
    (hF : Fam.Hyps) (hΓ : Zeta23.GammaFacts) (hMV : ∃ C : ℝ, 0 < C ∧ Zeta23.MVHilbert C)
    (hPP : PPInput) (hRvM : RiemannVonMangoldt Z) {cinf : ℝ} (hc0 : 0 < cinf)
    (hc : Tendsto (fun T => ThmD.cRatio (P.lam1 T) ((P.atV v T).a T) ((P.atV v T).b T)
        (JD Fam.D ((P.atV v T).g T) (P.L T) (l T))) atTop (𝓝 cinf)) :
    CoeffMoments Z (P.atV v) Fam cinf⁻¹ :=
  coeffMoments_of_family (Pf := P.atV v) hP hlam1 (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    hwin hF hΓ hMV hPP hRvM hc0 hc

end XiPrime
end Zeta23
