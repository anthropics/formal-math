/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Zeta23.ThmD.Mult
import Zeta23.Assembly.CertificateUnion
import Zeta23.Statement.Union

/-!
# Montgomery--Taylor bound for zeros that are simple or on the critical line
-/

noncomputable section

open Filter Asymptotics Topology Real RHLinalg

namespace Zeta23.ThmD

open Assembly

/-- Union proportion associated to a reciprocal second-moment parameter `c⁻¹`. -/
def unionProp (c : ℝ) : ℝ :=
  1 - (c⁻¹ - 1) / ZeroSide.unionQ

lemma unionQ_mul_unionProp (c : ℝ) :
    ZeroSide.unionQ * unionProp c =
      2 * ZeroSide.unionC - ZeroSide.unionQ - c⁻¹ := by
  have hq : ZeroSide.unionQ ≠ 0 := ZeroSide.unionQ_pos.ne'
  unfold unionProp
  field_simp
  nlinarith [ZeroSide.two_unionC_eq_one_add_two_unionQ]

section Abstract

/-- Montgomery--Taylor union theorem with all paper inputs explicit. -/
theorem thmD_union_abstract (Z : ZeroConfig) (H : PaperInputs Z)
    (P : Params) (hP : P.Valid)
    (aT bT JT trG trG2 : ℝ → ℝ)
    (hTr : TracesBoundsD P aT bT JT trG trG2
      (fun T => (Z.N T (2 * T) : ℝ)))
    {c : ℝ} (hc0 : 0 < c)
    (hc : Tendsto (fun T => cRatio (P.lam1 T) (aT T) (bT T) (JT T))
      atTop (𝓝 c))
    (ha : ∀ᶠ T in atTop, 1 / 2 ≤ aT T)
    (θ₀ : ℝ → ℝ)
    (hTail : ∀ᶠ T in atTop, TailInputs Z (P.atD T) T (θ₀ T))
    (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop,
      θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop,
      (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop, Z.Gz (P.atD T) T = (P.atD T).Gp T)
    (hId : ∀ᶠ T in atTop,
      (P.atD T).trGtilde T = trG T ∧
      (P.atD T).trGtildeSq T = trG2 T ∧
      (P.atD T).a T = aT T)
    (hcalE : Tendsto P.calE atTop (𝓝 0)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (unionProp c - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.Nu T (2 * T) := by
  have hlam0 := hP.lam_pos
  have hlam1 := hP.lam_le_one
  obtain ⟨C₁, hC₁, T₁, htr1⟩ := hTr.tr1
  obtain ⟨C₂, _, T₂, hfr2⟩ := hTr.frhat
  obtain ⟨Cθ, hθ⟩ := hθ₀
  obtain ⟨CII, hII⟩ := hNII
  set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hNdef
  set cinv : ℝ → ℝ := fun T =>
    (cRatio (P.lam1 T) (aT T) (bT T) (JT T))⁻¹ with hcinv
  set R₁ : ℝ → ℝ := fun T => C₁ * Real.sqrt (P.X T) / aT T with hR₁
  set R₂ : ℝ → ℝ := fun T => C₂ * P.calE T * (cinv T * N T) with hR₂
  set B : ℝ → ℝ := fun T => θ₀ T / (aT T * P.L T) with hBdef
  set err : ℝ → ℝ := fun T =>
    (2 * ZeroSide.unionC * R₁ T + R₂ T +
      2 * ZeroSide.unionQ * (NII Z T : ℝ) +
      B T * (2 * ZeroSide.unionC +
        2 * Real.sqrt (cinv T * N T + R₂ T) + B T)) +
      |cinv T - c⁻¹| * N T with herr
  have hcinv_to : Tendsto cinv atTop (𝓝 c⁻¹) := hc.inv₀ hc0.ne'
  have hmain : ∀ᶠ T in atTop,
      ZeroSide.unionQ * unionProp c * N T - err T
        ≤ ZeroSide.unionQ * (Z.Nu T (2 * T) : ℝ) := by
    filter_upwards [hTail, hGzGp, hId, ha,
      eventually_ge_atTop T₁, eventually_ge_atTop T₂,
      eventually_ge_atTop (0 : ℝ), eventually_l_pos, eventually_w8 hP]
      with T hTl hGG hid ha0 hT₁ hT₂ hT0 hl h8
    obtain ⟨hidtr, hidfr, hida⟩ := hid
    have hapos' : 0 < aT T := by linarith [ha0]
    have haposD : 0 < (P.atD T).a T := by rw [hida]; exact hapos'
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
    have hA := seamA_union hT0
      (fun z => GzGp.phiHat_conj _ T z)
      (fun r => GzGp.phiHat_ofReal _ T r)
      (poissonSqD hP h8) hTl haposD hLpos
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
    have htrLower : N T - R₁ T ≤ (aT T * P.L T)⁻¹ * trG T := by
      have := (abs_le.mp htr).1
      linarith
    have hfrb : ((aT T * P.L T)⁻¹) ^ 2 * trG2 T
        ≤ cinv T * N T + R₂ T := by
      have h := hfr2 T hT₂
      simp only at h
      have h1 : trG2 T / (aT T * P.L T) ^ 2 - cinv T * N T
          ≤ C₂ * P.calE T * (cinv T * N T) := by
        rw [← mul_assoc] at h
        exact le_trans (le_trans (le_max_left _ 0) (le_abs_self _)) h
      have e : ((aT T * P.L T)⁻¹) ^ 2 * trG2 T =
          trG2 T / (aT T * P.L T) ^ 2 := by
        rw [inv_pow, div_eq_inv_mul]
      rw [e]
      simp only [hR₂]
      linarith
    have hB₀ : 0 ≤ B T :=
      div_nonneg hTl.theta_nonneg (mul_pos hapos' hLpos).le
    have h := union_lower_moment hB₀ hA htrLower hfrb
    have hN0 : 0 ≤ N T := Nat.cast_nonneg _
    have hcd :
        (2 * ZeroSide.unionC - ZeroSide.unionQ - c⁻¹) * N T -
            |cinv T - c⁻¹| * N T
          ≤ (2 * ZeroSide.unionC - ZeroSide.unionQ - cinv T) * N T := by
      have h1 := mul_le_mul_of_nonneg_right
        (le_abs_self (cinv T - c⁻¹)) hN0
      linarith
    rw [unionQ_mul_unionProp] at *
    simp only [herr, hR₁, hR₂, hBdef, hNdef] at h hcd ⊢
    linarith
  have hNtop : Tendsto N atTop atTop := tendsto_N_atTop Z H.RvM
  have o1 : R₁ =o[atTop] N := by
    have hbd : (fun T => C₁ / aT T) =O[atTop] (fun _ => (1 : ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2 * C₁) ?_
      filter_upwards [ha] with T ha0
      rw [abs_of_nonneg (div_nonneg hC₁.le (by linarith [ha0]))]
      rw [div_le_iff₀ (by linarith [ha0])]
      nlinarith [ha0]
    have hx := isLittleO_of_bdd_mul hbd
      (isLittleO_N_of_isLittleO_Tl Z H.RvM
        (isLittleO_sqrtX_Tl P hlam0 hlam1))
    exact hx.congr_left fun T => by simp only [hR₁]; ring
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
      have hx := hcinvO.mul (isBigO_refl N atTop)
      simpa using hx
    have hx := ((isLittleO_one_iff ℝ).2 hcE0).mul_isBigO i1
    refine (hx.congr_left fun T => ?_).congr_right fun T => by simp
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
        (fun T => 2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T))
        atTop (𝓝 0) := by
      simpa using (tendsto_theta_over_L P hlam0 hlam1).const_mul (2 * |Cθ|)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hTail, ha, eventually_l_pos] with T hTl ha0 hl
      have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
      exact div_nonneg hTl.theta_nonneg (by nlinarith)
    · filter_upwards [hTail, ha, eventually_l_pos, hθ,
        eventually_gt_atTop (0 : ℝ)]
        with T hTl ha0 hl hθT hT0
      have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
      have hapos' : 0 < aT T := by linarith
      have hq : 0 ≤ l T * T ^ (P.lam / 2 - 1) / P.L T := by positivity
      simp only [hBdef]
      rw [div_le_iff₀ (mul_pos hapos' hLpos)]
      calc
        θ₀ T ≤ Cθ * l T * T ^ (P.lam / 2 - 1) := hθT
        _ ≤ |Cθ| * l T * T ^ (P.lam / 2 - 1) := by
          gcongr
          exact le_abs_self _
        _ = |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T := by
          field_simp
        _ ≤ (2 * |Cθ| *
            (l T * T ^ (P.lam / 2 - 1) / P.L T)) *
            (aT T * P.L T) := by
          have he : |Cθ| *
              (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T =
              (2 * |Cθ| *
                (l T * T ^ (P.lam / 2 - 1) / P.L T)) *
                (1 / 2 * P.L T) := by ring
          rw [he]
          gcongr
  have o5 := err_isLittleO (R₁ := R₁) (R₂ := R₂)
    (NII := fun T => (NII Z T : ℝ)) (B := B) (cl := cinv)
    hNtop o1 o2 o3 o4 hcinv_bd
  have oB : B =o[atTop] N := by
    refine ((isLittleO_one_iff ℝ).2 o4).trans_isBigO
      (IsBigO.of_bound 1 ?_)
    filter_upwards [hNtop.eventually_ge_atTop 1] with T h1
    rw [norm_one, Real.norm_eq_abs, abs_of_nonneg (by linarith), one_mul]
    exact h1
  have o5u : (fun T =>
      2 * ZeroSide.unionC * R₁ T + R₂ T +
      2 * ZeroSide.unionQ * (NII Z T : ℝ) +
      B T * (2 * ZeroSide.unionC +
        2 * Real.sqrt (cinv T * N T + R₂ T) + B T)) =o[atTop] N := by
    have hx := o5.add
      (((o1.const_mul_left (2 * ZeroSide.unionC - 4)).add
        (o3.const_mul_left (2 * ZeroSide.unionQ - 3))).add
        (oB.const_mul_left (2 * ZeroSide.unionC - 4)))
    exact hx.congr_left fun T => by ring
  have o6 : (fun T => |cinv T - c⁻¹| * N T) =o[atTop] N := by
    refine isLittleO_of_tendsto_zero_mul ?_
    have hx : Tendsto (fun T => cinv T - c⁻¹) atTop (𝓝 0) := by
      simpa using hcinv_to.sub_const c⁻¹
    simpa using hx.abs
  have herr_o : err =o[atTop] N := o5u.add o6
  have hscaled := eps_form_of_isLittleO hmain
    (Eventually.of_forall fun T => Nat.cast_nonneg _) herr_o
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := hscaled (ZeroSide.unionQ * ε)
    (mul_pos ZeroSide.unionQ_pos hε)
  refine ⟨T₀, fun T hT => ?_⟩
  have h := hT₀ T hT
  have hqscaled : ZeroSide.unionQ *
      ((unionProp c - ε) * N T) ≤
      ZeroSide.unionQ * (Z.Nu T (2 * T) : ℝ) := by
    calc
      ZeroSide.unionQ * ((unionProp c - ε) * N T) =
          (ZeroSide.unionQ * unionProp c - ZeroSide.unionQ * ε) * N T := by
        ring
      _ ≤ ZeroSide.unionQ * (Z.Nu T (2 * T) : ℝ) := h
  have := le_of_mul_le_mul_left hqscaled ZeroSide.unionQ_pos
  simpa only [hNdef] using this

end Abstract

/-- Exact relation between the union rate and the existing `HD` rate. -/
lemma unionProp_cStar_eq (lam : ℝ) :
    unionProp (cStar lam) = 1 + (HD lam - 1) / ZeroSide.unionQ := by
  unfold unionProp HD
  ring

/-- The reciprocal Montgomery--Taylor endpoint constant in trigonometric form. -/
theorem cStar_one_inv_eq_montgomeryTaylor :
    (cStar 1)⁻¹ = 1 / 2 + (Real.sqrt 2)⁻¹ *
      (Real.cos (Real.sqrt 2)⁻¹ / Real.sin (Real.sqrt 2)⁻¹) := by
  calc
    (cStar 1)⁻¹ = 2 - HD 1 := by
      unfold HD
      ring
    _ = 1 / 2 + (Real.sqrt 2)⁻¹ *
        (Real.cos (Real.sqrt 2)⁻¹ / Real.sin (Real.sqrt 2)⁻¹) := by
      rw [HD_one]
      ring

/-- Fixed bandwidth `0 < λ ≤ 1`, for an abstract zero configuration. -/
theorem thmD_union_lam_abstract (Z : ZeroConfig) (H : PaperInputs Z)
    (P : Params) (hP : P.Valid) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (unionProp (cStar P.lam) - ε) * (Z.N T (2 * T) : ℝ)
        ≤ Z.Nu T (2 * T) := by
  have hLoc : LocalHypsCoreDEventually P := localHypsCoreD_eventually hP
  have hTr := tracesBoundsD_concrete (Z := Z) hP H hLoc
  have hc := tendsto_cRatio_concrete hP Z
  have hc0 := cStar_pos hP.lam_pos hP.lam_le_one
  have ha : ∀ᶠ T in atTop, 1 / 2 ≤ (concreteDataD P Z).aT T :=
    (concreteFactsD hP H hLoc).ab_range.mono fun _ h => h.1.trans h.2.1
  obtain ⟨θ₀, hTail, hθ₀⟩ := eventually_tailPackageD Z H hP
  obtain ⟨A₀, hA₀, hloc⟩ := H.RvM.local_count
  have hNII := Tail.eventually_NII_le Z hA₀ hloc
  have hGzGp := eventually_GzGpD Z H hP
  have hId : ∀ᶠ T in atTop,
      (P.atD T).trGtilde T = (concreteDataD P Z).trG T ∧
      (P.atD T).trGtildeSq T = (concreteDataD P Z).trG2 T ∧
      (P.atD T).a T = (concreteDataD P Z).aT T :=
    Eventually.of_forall fun T =>
      ⟨Params.atD_trGtilde T hP, Params.atD_trGtildeSq T hP,
        Params.atD_a T hP⟩
  have hcalE := calE_tendsto_zero P hP.lam_pos hP.lam_le_one
    (zero_le_one.trans hP.one_le_w)
  exact thmD_union_abstract Z H P hP _ _ _ _ _ hTr hc0 hc ha
    θ₀ hTail hθ₀ hNII hGzGp hId hcalE

/-- Zeta at fixed bandwidth `0 < λ ≤ 1`, unconditionally. -/
theorem thmD_union_lam {lam : ℝ} (h0 : 0 < lam) (h1 : lam ≤ 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (unionProp (cStar lam) - ε) * (Ncount T (2 * T) : ℝ) ≤
        ((N0 T (2 * T) + Nsimple T (2 * T) - N0simple T (2 * T) : ℕ) : ℝ) := by
  have hP := paramsOf_valid taperProfile_stdProfile h0 h1
  simpa only [paramsOf, zetaZeroConfig_N, zetaZeroConfig_Nu_eq] using
    thmD_union_lam_abstract zetaZeroConfig paperInputs_zeta
      (paramsOf stdProfile lam) hP

/-- **In `T < Im ρ ≤ 2T`, at least
`unionProp (cStar 1) = 0.8876200081...` of zeta-zero multiplicity units are
simple or on the critical line, unconditionally.**  This theorem uses the exact
symbolic constant; `UnionDecimal.lean` supplies a certified decimal enclosure. -/
theorem thmD₀_union :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (unionProp (cStar 1) - ε) * (Ncount T (2 * T) : ℝ) ≤
        ((N0 T (2 * T) + Nsimple T (2 * T) - N0simple T (2 * T) : ℕ) : ℝ) :=
  thmD_union_lam (lam := 1) zero_lt_one le_rfl

/-- The same theorem with the exact Montgomery--Taylor constant written out. -/
theorem thmD₀_union' :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (1 + (1 / 2 - (Real.sqrt 2)⁻¹ *
          (Real.cos (Real.sqrt 2)⁻¹ / Real.sin (Real.sqrt 2)⁻¹)) /
          (3 / 2 + Real.sqrt 2) - ε) * (Ncount T (2 * T) : ℝ) ≤
        ((N0 T (2 * T) + Nsimple T (2 * T) - N0simple T (2 * T) : ℕ) : ℝ) := by
  have hconst : 1 + (1 / 2 - (Real.sqrt 2)⁻¹ *
      (Real.cos (Real.sqrt 2)⁻¹ / Real.sin (Real.sqrt 2)⁻¹)) /
      (3 / 2 + Real.sqrt 2) = unionProp (cStar 1) := by
    rw [unionProp_cStar_eq, HD_one]
    unfold ZeroSide.unionQ
    ring
  rw [hconst]
  exact thmD₀_union

/-- Cumulative form: the same simple-or-on-line multiplicity proportion in `0 < Im ρ ≤ T`. -/
theorem thmD₀_union_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (unionProp (cStar 1) - ε) * (Ncount 0 T : ℝ) ≤
        ((N0 0 T + Nsimple 0 T - N0simple 0 T : ℕ) : ℝ) := by
  apply cumulative_of_dyadic zetaSeam paperInputs_zeta.RvM
      (f := fun a b => N0 a b + Nsimple a b - N0simple a b)
      (fun a b d hab hbd => ?_) thmD₀_union
  simpa only [zetaZeroConfig_Nu_eq] using
    Assembly.Nu_add zetaZeroConfig hab hbd

end Zeta23.ThmD
