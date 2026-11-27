/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.Assembly.SeamSextuple
import Zeta23.ThmD.Sextuple.Final
import Zeta23.ThmD.Concrete
import Zeta23.ThmD.ZeroSideD
import Zeta23.ThmD.Limit

/-!
# The unconditional Montgomery--Taylor base with sextuple penalty

This file runs the multiplicity-aware Theorem-D trace pipeline while retaining
`ZeroSide.simpleSextuplePenalty` with a positive sign.  `baseError` records the
trace, Hilbert--Schmidt, enlarged-interval collar, tail, and ratio-drift losses
as one explicit function.
-/

noncomputable section

open Filter Asymptotics Topology Real RHLinalg

namespace Zeta23
namespace ThmD
namespace Sextuple

open Assembly

/-- The complete error in the penalty-retaining Montgomery--Taylor base bound.
The five displayed summands are respectively the trace loss, Hilbert--Schmidt
loss, collar loss, tail perturbation, and limiting-ratio drift. -/
def baseError (Z : ZeroConfig) (P : Params)
    (aT bT JT θ₀ : ℝ → ℝ) (c C₁ C₂ : ℝ) : ℝ → ℝ := fun T =>
  4 * (C₁ * Real.sqrt (P.X T) / aT T)
    + C₂ * P.calE T
        * ((cRatio (P.lam1 T) (aT T) (bT T) (JT T))⁻¹
          * (Z.N T (2 * T) : ℝ))
    + 3 * (NII Z T : ℝ)
    + (θ₀ T / (aT T * P.L T))
        * (4 + 2 * Real.sqrt
            ((cRatio (P.lam1 T) (aT T) (bT T) (JT T))⁻¹
                * (Z.N T (2 * T) : ℝ)
              + C₂ * P.calE T
                  * ((cRatio (P.lam1 T) (aT T) (bT T) (JT T))⁻¹
                    * (Z.N T (2 * T) : ℝ)))
          + θ₀ T / (aT T * P.L T))
    + |(cRatio (P.lam1 T) (aT T) (bT T) (JT T))⁻¹ - c⁻¹|
        * (Z.N T (2 * T) : ℝ)

/-- Abstract penalty-retaining base pipeline.  Unlike the older epsilon-form
wrapper, this theorem returns the actual `o(N)` error function. -/
theorem exists_basePenaltyInterface_abstract
    (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid)
    (aT bT JT trG trG2 : ℝ → ℝ)
    (hTr : TracesBoundsD P aT bT JT trG trG2
      (fun T => (Z.N T (2 * T) : ℝ)))
    {c : ℝ} (hc0 : 0 < c)
    (hc : Tendsto
      (fun T => cRatio (P.lam1 T) (aT T) (bT T) (JT T)) atTop (𝓝 c))
    (ha : ∀ᶠ T in atTop, 1 / 2 ≤ aT T ∧ aT T ≤ 1)
    (θ₀ : ℝ → ℝ)
    (hTail : ∀ᶠ T in atTop, TailInputs Z (P.atD T) T (θ₀ T))
    (hθ₀ : ∃ C : ℝ,
      ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ,
      ∀ᶠ T in atTop, (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop, Z.Gz (P.atD T) T = (P.atD T).Gp T)
    (hId : ∀ᶠ T in atTop,
      (P.atD T).trGtilde T = trG T ∧
      (P.atD T).trGtildeSq T = trG2 T ∧
      (P.atD T).a T = aT T)
    (hcalE : Tendsto P.calE atTop (𝓝 0)) :
    ∃ C₁ C₂ : ℝ,
      BasePenaltyInterface (2 - c⁻¹)
        (fun T => (Z.N T (2 * T) : ℝ))
        (fun T => (Z.N0s T (2 * T) : ℝ))
        (fun T => ZeroSide.simpleSextuplePenalty Z T (P.atD T))
        (baseError Z P aT bT JT θ₀ c C₁ C₂) := by
  have hlam0 := hP.lam_pos
  have hlam1 := hP.lam_le_one
  obtain ⟨C₁, hC₁, T₁, htr1⟩ := hTr.tr1
  obtain ⟨C₂, hC₂, T₂, hfr2⟩ := hTr.frhat
  obtain ⟨Cθ, hθ⟩ := hθ₀
  obtain ⟨CII, hII⟩ := hNII
  set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hNdef
  set cinv : ℝ → ℝ := fun T =>
    (cRatio (P.lam1 T) (aT T) (bT T) (JT T))⁻¹ with hcinv
  set R₁ : ℝ → ℝ := fun T => C₁ * Real.sqrt (P.X T) / aT T with hR₁
  set R₂ : ℝ → ℝ := fun T => C₂ * P.calE T * (cinv T * N T) with hR₂
  set B : ℝ → ℝ := fun T => θ₀ T / (aT T * P.L T) with hBdef
  have hcinv_to : Tendsto cinv atTop (𝓝 c⁻¹) := hc.inv₀ hc0.ne'
  have hmain : ∀ᶠ T in atTop,
      (2 - c⁻¹) * N T
          + ZeroSide.simpleSextuplePenalty Z T (P.atD T)
          - baseError Z P aT bT JT θ₀ c C₁ C₂ T
        ≤ (Z.N0s T (2 * T) : ℝ) := by
    filter_upwards [hTail, hGzGp, hId, ha, eventually_ge_atTop T₁,
      eventually_ge_atTop T₂, eventually_ge_atTop (0 : ℝ),
      eventually_l_pos, eventually_calE_nonneg P hlam0
        (zero_le_one.trans hP.one_le_w), eventually_w8 hP]
      with T hTl hGG hid ha2 hT₁ hT₂ hT0 hl hE0 h8
    obtain ⟨hidtr, hidfr, hida⟩ := hid
    have hapos' : 0 < aT T := by linarith [ha2.1]
    have haposD : 0 < (P.atD T).a T := by rw [hida]; exact hapos'
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
    have hA := seamA_sextuple hT0 (poissonSqD hP h8) hTl haposD hLpos
    have hrt : rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T)) =
        (aT T * P.L T)⁻¹ * trG T := by
      rw [rtrace_hat, hGG, rtrace_tilde_Gp, hidtr, hida]
      rfl
    have hfr : frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T)) =
        ((aT T * P.L T)⁻¹) ^ 2 * trG2 T := by
      rw [frobSq_hat, hGG, frobSq_tilde_Gp, hidfr, hida]
      rfl
    have haL : (P.atD T).a T * (P.atD T).L T = aT T * P.L T := by
      rw [hida]
      rfl
    rw [hrt, hfr, haL] at hA
    have htr : |(aT T * P.L T)⁻¹ * trG T - N T| ≤ R₁ T :=
      trGhat_sub_N_le hapos' hLpos (by simpa only using htr1 T hT₁)
    have hfrb : ((aT T * P.L T)⁻¹) ^ 2 * trG2 T ≤
        cinv T * N T + R₂ T := by
      have h := hfr2 T hT₂
      simp only at h
      have h1 : trG2 T / (aT T * P.L T) ^ 2 - cinv T * N T ≤
          C₂ * P.calE T * (cinv T * N T) := by
        rw [← mul_assoc] at h
        exact le_trans (le_trans (le_max_left _ 0) (le_abs_self _)) h
      have heq : ((aT T * P.L T)⁻¹) ^ 2 * trG2 T =
          trG2 T / (aT T * P.L T) ^ 2 := by
        rw [inv_pow, div_eq_inv_mul]
      rw [heq]
      simp only [hR₂]
      linarith
    have hB₀ : 0 ≤ B T :=
      div_nonneg hTl.theta_nonneg (mul_pos hapos' hLpos).le
    have hA' :
        4 * ((aT T * P.L T)⁻¹ * trG T)
            - (((aT T * P.L T)⁻¹) ^ 2 * trG2 T)
            - 2 * (Z.N T (2 * T) : ℝ) - 3 * (NII Z T : ℝ)
            - B T *
                (4 + 2 * Real.sqrt
                    (((aT T * P.L T)⁻¹) ^ 2 * trG2 T) + B T)
          ≤ (Z.N0s T (2 * T) : ℝ)
              - ZeroSide.simpleSextuplePenalty Z T (P.atD T) := by
      simp only [hBdef]
      linarith [hA]
    have h := N0star_lower_c hB₀ hA' htr hfrb
    have hN0 : 0 ≤ N T := Nat.cast_nonneg _
    have hcd :
        (2 - c⁻¹) * N T - |cinv T - c⁻¹| * N T ≤
          (2 - cinv T) * N T := by
      have h1 := mul_le_mul_of_nonneg_right
        (le_abs_self (cinv T - c⁻¹)) hN0
      linarith [h1]
    simp only [baseError, hR₁, hR₂, hBdef, hcinv, hNdef] at h hcd ⊢
    linarith
  have hNtop : Tendsto N atTop atTop := tendsto_N_atTop Z H.RvM
  have o1 : R₁ =o[atTop] N := by
    have hbd : (fun T => C₁ / aT T) =O[atTop] (fun _ => (1 : ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2 * C₁) ?_
      filter_upwards [ha] with T ha2
      rw [abs_of_nonneg (div_nonneg hC₁.le (by linarith [ha2.1]))]
      rw [div_le_iff₀ (by linarith [ha2.1])]
      nlinarith [ha2.1]
    have h := isLittleO_of_bdd_mul hbd
      (isLittleO_N_of_isLittleO_Tl Z H.RvM
        (isLittleO_sqrtX_Tl P hlam0 hlam1))
    exact h.congr_left fun T => by simp only [hR₁]; ring
  have hcinv_bd : ∀ᶠ T in atTop, 0 ≤ cinv T ∧ cinv T ≤ 2 * c⁻¹ := by
    have hcpos : (0 : ℝ) < c⁻¹ := inv_pos.mpr hc0
    filter_upwards [hcinv_to.eventually (eventually_ge_nhds hcpos),
      hcinv_to.eventually
        (eventually_le_nhds (show c⁻¹ < 2 * c⁻¹ by linarith))]
      with T h1 h2
    exact ⟨h1, h2⟩
  have hcinvO : cinv =O[atTop] (fun _ => (1 : ℝ)) := by
    refine isBigO_one_of_abs_le (C := 2 * c⁻¹) ?_
    filter_upwards [hcinv_bd] with T h
    rw [abs_of_nonneg h.1]
    exact h.2
  have o2 : R₂ =o[atTop] N := by
    have hcE0 : Tendsto (fun T => C₂ * P.calE T) atTop (𝓝 0) := by
      simpa using hcalE.const_mul C₂
    have i1 : (fun T => cinv T * N T) =O[atTop] N := by
      have h := hcinvO.mul (isBigO_refl N atTop)
      simpa using h
    have h := ((isLittleO_one_iff ℝ).2 hcE0).mul_isBigO i1
    refine (h.congr_left fun T => ?_).congr_right fun T => by simp
    simp only [hR₂]
  have o3 : (fun T => (NII Z T : ℝ)) =o[atTop] N := by
    have hO : (fun T => (NII Z T : ℝ)) =O[atTop]
        (fun T => Real.sqrt T * l T) := by
      refine IsBigO.of_bound CII ?_
      filter_upwards [hII, eventually_l_pos] with T h hl
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)]
      simpa [mul_assoc] using h
    exact hO.trans_isLittleO
      (isLittleO_N_of_isLittleO_Tl Z H.RvM isLittleO_sqrt_mul_l_Tl)
  have o4 : Tendsto B atTop (𝓝 0) := by
    have hup : Tendsto
        (fun T => 2 * |Cθ| *
          (l T * T ^ (P.lam / 2 - 1) / P.L T)) atTop (𝓝 0) := by
      simpa using
        (tendsto_theta_over_L P hlam0 hlam1).const_mul (2 * |Cθ|)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hTail, ha, eventually_l_pos] with T hTl ha2 hl
      have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
      exact div_nonneg hTl.theta_nonneg (by nlinarith [ha2.1])
    · filter_upwards [hTail, ha, eventually_l_pos, hθ,
        eventually_gt_atTop (0 : ℝ)] with T hTl ha2 hl hθT hT0
      have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
      have hapos' : 0 < aT T := by linarith [ha2.1]
      have hq : 0 ≤ l T * T ^ (P.lam / 2 - 1) / P.L T := by positivity
      simp only [hBdef]
      rw [div_le_iff₀ (mul_pos hapos' hLpos)]
      calc
        θ₀ T ≤ Cθ * l T * T ^ (P.lam / 2 - 1) := hθT
        _ ≤ |Cθ| * l T * T ^ (P.lam / 2 - 1) := by
          gcongr
          exact le_abs_self _
        _ = |Cθ| *
            (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T := by
          field_simp
        _ ≤ (2 * |Cθ| *
            (l T * T ^ (P.lam / 2 - 1) / P.L T))
              * (aT T * P.L T) := by
          have heq : |Cθ| *
                (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T =
              (2 * |Cθ| *
                (l T * T ^ (P.lam / 2 - 1) / P.L T))
                  * (1 / 2 * P.L T) := by ring
          rw [heq]
          gcongr
          exact ha2.1
  have o5 := err_isLittleO
    (R₁ := R₁) (R₂ := R₂) (NII := fun T => (NII Z T : ℝ))
    (B := B) (cl := cinv) hNtop o1 o2 o3 o4 hcinv_bd
  have o6 : (fun T => |cinv T - c⁻¹| * N T) =o[atTop] N := by
    refine isLittleO_of_tendsto_zero_mul ?_
    have h : Tendsto (fun T => cinv T - c⁻¹) atTop (𝓝 0) := by
      simpa using hcinv_to.sub_const c⁻¹
    simpa using h.abs
  have herr : baseError Z P aT bT JT θ₀ c C₁ C₂ =o[atTop] N := by
    refine (o5.add o6).congr_left fun T => ?_
    simp only [baseError, hR₁, hR₂, hBdef, hcinv, hNdef]
  refine ⟨C₁, C₂, ?_⟩
  exact ⟨by simpa only [hNdef] using hmain,
    by simpa only [hNdef] using herr⟩

/-- The three pieces of data selected from the proved analytic estimates. -/
structure ZetaBaseErrorData where
  traceConstant : ℝ
  hilbertSchmidtConstant : ℝ
  theta : ℝ → ℝ

/-- The canonical Montgomery--Taylor parameter family at `lambda = 1`. -/
def montgomeryTaylorParams : Params := paramsOf stdProfile 1

/-- The proof-free spectral penalty used by both sides of the sextuple
feedback argument. -/
def zetaSextuplePenalty (T : ℝ) : ℝ :=
  ZeroSide.simpleSextuplePenalty zetaZeroConfig T
    (montgomeryTaylorParams.atD T)

/-- The explicit zeta error associated to selected proved constants. -/
def zetaBaseErrorOf (D : ZetaBaseErrorData) : ℝ → ℝ :=
  baseError zetaZeroConfig montgomeryTaylorParams
    (concreteDataD montgomeryTaylorParams zetaZeroConfig).aT
    (concreteDataD montgomeryTaylorParams zetaZeroConfig).bT
    (concreteDataD montgomeryTaylorParams zetaZeroConfig).JT
    D.theta (cStar 1) D.traceConstant D.hilbertSchmidtConstant

/-- Existing proved paper inputs select constants for which the explicit error
and the proof-free penalty satisfy the base interface. -/
theorem exists_zetaBaseErrorData :
    ∃ D : ZetaBaseErrorData,
      ZetaBasePenaltyInterface zetaSextuplePenalty (zetaBaseErrorOf D) := by
  let P : Params := montgomeryTaylorParams
  have hP : P.Valid := by
    dsimp [P, montgomeryTaylorParams]
    exact paramsOf_valid taperProfile_stdProfile (by norm_num) (by norm_num)
  have hLoc : LocalHypsCoreDEventually P := localHypsCoreD_eventually hP
  have hTr := tracesBoundsD_concrete (Z := zetaZeroConfig) hP paperInputs_zeta hLoc
  have hc := tendsto_cRatio_concrete hP zetaZeroConfig
  have hc0 := cStar_pos hP.lam_pos hP.lam_le_one
  have ha : ∀ᶠ T in atTop,
      1 / 2 ≤ (concreteDataD P zetaZeroConfig).aT T ∧
      (concreteDataD P zetaZeroConfig).aT T ≤ 1 :=
    (concreteFactsD hP paperInputs_zeta hLoc).ab_range.mono
      fun T h => ⟨h.1.trans h.2.1, h.2.2.1⟩
  obtain ⟨θ₀, hTail, hθ₀⟩ :=
    eventually_tailPackageD zetaZeroConfig paperInputs_zeta hP
  obtain ⟨A₀, hA₀, hloc⟩ := paperInputs_zeta.RvM.local_count
  have hNII := Tail.eventually_NII_le zetaZeroConfig hA₀ hloc
  have hGzGp := eventually_GzGpD zetaZeroConfig paperInputs_zeta hP
  have hId : ∀ᶠ T in atTop,
      (P.atD T).trGtilde T = (concreteDataD P zetaZeroConfig).trG T ∧
      (P.atD T).trGtildeSq T = (concreteDataD P zetaZeroConfig).trG2 T ∧
      (P.atD T).a T = (concreteDataD P zetaZeroConfig).aT T :=
    Eventually.of_forall fun T =>
      ⟨Params.atD_trGtilde T hP, Params.atD_trGtildeSq T hP,
        Params.atD_a T hP⟩
  have hcalE := calE_tendsto_zero P hP.lam_pos hP.lam_le_one
    (zero_le_one.trans hP.one_le_w)
  obtain ⟨C₁, C₂, hbase⟩ := exists_basePenaltyInterface_abstract
    zetaZeroConfig paperInputs_zeta P hP
    (concreteDataD P zetaZeroConfig).aT
    (concreteDataD P zetaZeroConfig).bT
    (concreteDataD P zetaZeroConfig).JT
    (concreteDataD P zetaZeroConfig).trG
    (concreteDataD P zetaZeroConfig).trG2 hTr hc0 hc ha
    θ₀ hTail hθ₀ hNII hGzGp hId hcalE
  refine ⟨⟨C₁, C₂, θ₀⟩, ?_⟩
  change ZetaBasePenaltyInterface
    (fun T => ZeroSide.simpleSextuplePenalty zetaZeroConfig T
      (montgomeryTaylorParams.atD T))
    (zetaBaseErrorOf ⟨C₁, C₂, θ₀⟩)
  simpa [ZetaBasePenaltyInterface, zetaBaseErrorOf, P,
    montgomeryTaylorParams, HD, one_div, paramsOf] using hbase

/-- Canonical selected data; only already-proved estimates enter the choice. -/
noncomputable def zetaBaseErrorData : ZetaBaseErrorData :=
  Classical.choose exists_zetaBaseErrorData

/-- The one explicit `o(N)` remainder used by the zeta base interface. -/
def zetaBaseError : ℝ → ℝ := zetaBaseErrorOf zetaBaseErrorData

/-- **Unconditional sextuple base interface for zeta.** -/
theorem zetaBasePenaltyInterface :
    ZetaBasePenaltyInterface zetaSextuplePenalty zetaBaseError := by
  exact Classical.choose_spec exists_zetaBaseErrorData

/-- The explicit base remainder is `o(N(T,2T))`. -/
theorem zetaBaseError_isLittleO :
    zetaBaseError =o[atTop] (fun T => (Ncount T (2 * T) : ℝ)) :=
  zetaBasePenaltyInterface.error_isLittleO

/-- The strengthened Montgomery--Taylor base inequality with the proof-free
spectral penalty retained with positive sign. -/
theorem zetaBasePenalty_lower_bound :
    ∀ᶠ T in atTop,
      HD 1 * (Ncount T (2 * T) : ℝ) + zetaSextuplePenalty T
          - zetaBaseError T
        ≤ N0simple T (2 * T) :=
  zetaBasePenaltyInterface.lower_bound

end Sextuple
end ThmD
end Zeta23

end
