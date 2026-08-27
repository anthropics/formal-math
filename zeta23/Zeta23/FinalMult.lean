/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/FinalMult.lean — Theorems B and C of the paper with their stated constants 2/3 and 5/6
(the multiplicity-aware forms): running the §6 certificate on the multiplicity-aware rank–trace
inequalities of Assembly/SeamMult.lean (parameter c = 2 ⇒ N₀ˢ, c = 3 ⇒ N_d) with the SAME second
moment κ(λ) = 1/λ + λ/3 as Theorem A gives, for Mathlib's riemannZeta with NO hypotheses,

  thmB₀_mult : ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (2/3 − ε)·N(T,2T) ≤ N₀ˢ(T,2T)   (simple AND on the line),
  thmC₀_mult : ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (5/6 − ε)·N(T,2T) ≤ N_d(T,2T)    (distinct),

(Zeta23/Final.lean has the Cauchy–Schwarz forms of the same statements, with 1/2 and 3/4)
plus the fixed-λ forms (constants H(λ) = 2 − κ(λ) and G(λ) := 3/2 − κ(λ)/2) and cumulative forms.
-/
import Zeta23.Final
import Zeta23.Assembly.SeamMult
import Zeta23.Assembly.Certificate
import Zeta23.Assembly.CertificateC3
import Zeta23.ZeroSide.Final
import Zeta23.ThmD.Limit

noncomputable section

open Filter Asymptotics Topology Real RHLinalg

namespace Zeta23

open Assembly

/-- κ(λ) := 1/λ + λ/3, the second-moment constant of [eq:tr2]/[eq:ratio] (so H(λ) = 2 − κ(λ)). -/
def kfun (lam : ℝ) : ℝ := 1 / lam + lam / 3

/-- G(λ) := 3/2 − κ(λ)/2 — the c = 3 certificate constant; G(1) = 5/6. -/
def Gfun (lam : ℝ) : ℝ := 3 / 2 - kfun lam / 2

lemma Hfun_eq_two_sub_kfun (lam : ℝ) : Hfun lam = 2 - kfun lam := by
  simp only [Hfun, kfun]; ring

/-- near λ = 1: G(λ) ≥ 5/6 − (1 − λ) for 1/2 ≤ λ ≤ 1. -/
lemma Gfun_ge_near_one (lam : ℝ) (h1 : 1 / 2 ≤ lam) (h2 : lam ≤ 1) :
    5 / 6 - (1 - lam) ≤ Gfun lam := by
  simp only [Gfun, kfun]
  have h0 : 0 < lam := by linarith
  -- 5/6 − (1−λ) ≤ 3/2 − (1/λ + λ/3)/2: multiply through by λ > 0 and compare polynomials
  have key : (5 / 6 - (1 - lam)) * lam ≤ (3 / 2 - (1 / lam + lam / 3) / 2) * lam := by
    have e : (3 / 2 - (1 / lam + lam / 3) / 2) * lam = 3 / 2 * lam - 1 / 2 - lam ^ 2 / 6 := by
      field_simp; ring
    rw [e]
    nlinarith
  exact le_of_mul_le_mul_right key h0

/-- ε-form sup for G: constant 5/6 = sup_{λ<1} G(λ). -/
theorem eps_form_fiveSixths {N lower : ℝ → ℝ} (hN : ∀ T, 0 ≤ N T)
    (h : ∀ lam : ℝ, 1 / 2 ≤ lam → lam < 1 →
      ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (Gfun lam - ε) * N T ≤ lower T) :
    ∀ ε > 0, ∃ T₀, ∀ T ≥ T₀, (5 / 6 - ε) * N T ≤ lower T :=
  Assembly.eps_form_sup_half (fun η hη => by
    obtain ⟨lam, h1, h2, h3⟩ := Assembly.exists_lam_near_one hη
    exact ⟨lam, h1, h2, by linarith [Gfun_ge_near_one lam h1 h2.le]⟩) hN h

/-! ## The moment hypotheses from [thm:traces] (abstract zero configuration) -/

section Moments

variable (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid) (hlam : P.lam < 1)
  (hTr : ThmTracesHyp P Z)
  (hGzGp : ∀ᶠ T in atTop, Z.Gz P T = P.Gp T)
  (ha : ∀ᶠ T in atTop, 1 - 2 * P.w / P.L T ≤ P.a T ∧ P.a T ≤ 1)

include H hP hlam hTr hGzGp ha in
/-- [thm:traces] + H-RvM ⟹ the two moment hypotheses of the certificate with κ = κ(λ):
tr Ĝ ≥ (1 − δ)N and ‖Ĝ‖_F² ≤ (κ(λ) + δ)N eventually, for every δ > 0. -/
theorem moments_of_traces :
    (∀ δ > (0:ℝ), ∀ᶠ T in atTop, (1 - δ) * (Z.N T (2 * T) : ℝ) ≤ rtrace (P.hat T (Z.Gz P T))) ∧
    (∀ δ > (0:ℝ), ∀ᶠ T in atTop,
      frobSq (P.hat T (Z.Gz P T)) ≤ (kfun P.lam + δ) * (Z.N T (2 * T) : ℝ)) := by
  have hlam0 := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hlam.le
  have hw0 : 0 ≤ P.w := zero_le_one.trans hP.one_le_w
  have hcalE := calE_tendsto_zero P hlam0 hlam1 hw0
  have hTrE := hTr.toE
  obtain ⟨C₁, hC₁, T₁, htr1⟩ := hTrE.tr1
  obtain ⟨C₂, hC₂, T₂, htr2⟩ := hTrE.tr2
  obtain ⟨CN, T₃, hRvM⟩ := H.RvM.main
  set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hNdef
  set cl : ℝ → ℝ := fun T => 1 / P.lam1 T + P.lam1 T / 3 with hcl
  set K : ℝ → ℝ := fun T => (1 + C₂ * P.calE T) / P.a T ^ 2 with hK
  set R₁ : ℝ → ℝ := fun T => C₁ * Real.sqrt (P.X T) / P.a T with hR₁
  set R₂ : ℝ → ℝ := fun T => cl T * ((K T - 1) * N T + K T * (|CN| * Real.log T)) with hR₂
  have hLtop := tendsto_L_atTop P hlam0
  have ha1 := tendsto_a_one P hlam0 ha
  have hapos : ∀ᶠ T in atTop, 1 / 2 ≤ P.a T := by
    filter_upwards [ha, hLtop.eventually_ge_atTop (4 * P.w)] with T h hL4
    have hw := hP.one_le_w
    have hLpos : 0 < P.L T := by linarith
    have : 2 * P.w / P.L T ≤ 1 / 2 := by rw [div_le_iff₀ hLpos]; linarith
    linarith [h.1]
  have hcE0 : Tendsto (fun T => C₂ * P.calE T) atTop (𝓝 0) := by
    simpa using hcalE.const_mul C₂
  have hKto : Tendsto K atTop (𝓝 1) := by
    have h1 : Tendsto (fun T => 1 + C₂ * P.calE T) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add hcE0
    have h2 : Tendsto (fun T => P.a T ^ 2) atTop (𝓝 1) := by simpa using ha1.pow 2
    simpa [hK, Pi.div_def] using h1.div h2 one_ne_zero
  -- pointwise: seam B at every large T
  have hpt : ∀ᶠ T in atTop, |rtrace (P.hat T (Z.Gz P T)) - N T| ≤ R₁ T ∧
      frobSq (P.hat T (Z.Gz P T)) ≤ cl T * N T + R₂ T := by
    filter_upwards [hGzGp, hapos, eventually_ge_atTop T₁, eventually_ge_atTop T₂,
      eventually_ge_atTop T₃, eventually_gt_atTop (0:ℝ), eventually_l_pos, eventually_log_nonneg,
      hcE0.eventually (eventually_gt_nhds (show (-1:ℝ) < 0 by norm_num))]
      with T hGG ha2 hT₁ hT₂ hT₃ hT0 hl hlog hcE
    have hapos' : 0 < P.a T := by linarith
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
    have hℓ₁ := ell1_pos hl
    have hKnn : 0 ≤ 1 + C₂ * P.calE T := by linarith
    have htr2' : P.trGtildeSq T - P.mainTr2 T ≤ C₂ * P.calE T * P.mainTr2 T := by
      have := htr2 T hT₂
      simp only at this
      rw [← mul_assoc] at this
      exact (le_abs_self _).trans this
    have htr1' : |P.trGtilde T - P.a T * P.L T * (Z.N T (2 * T) : ℝ)|
        ≤ C₁ * (P.L T * Real.sqrt (P.X T)) := by
      have := htr1 T hT₁; simpa only using this
    have hRvM' : T * ell1 T / (2 * Real.pi) ≤ N T + |CN| * Real.log T := by
      have h1 := (abs_le.mp (hRvM T hT₃)).1
      have h2 : CN * Real.log T ≤ |CN| * Real.log T :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hlog
      have h3 : T / (2 * Real.pi) * ell1 T = T * ell1 T / (2 * Real.pi) := by ring
      simp only [hNdef]; linarith
    have hSB := seamB hGG hapos' hLpos hℓ₁ htr1' hKnn htr2' hRvM'
    refine ⟨?_, ?_⟩
    · simpa only [hR₁, hNdef] using hSB.1
    · have := hSB.2
      simp only [hR₂, hcl, hK, hNdef] at this ⊢
      linarith
  -- R₁, R₂ = o(N)  (as in Assembly.thmA_abstract_err)
  have hR := H.RvM
  have o1 : R₁ =o[atTop] N := by
    have hbd : (fun T => C₁ / P.a T) =O[atTop] (fun _ => (1:ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2 * C₁) ?_
      filter_upwards [hapos] with T ha2
      rw [abs_of_nonneg (div_nonneg hC₁.le (by linarith))]
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have := isLittleO_of_bdd_mul hbd
      (isLittleO_N_of_isLittleO_Tl Z hR (isLittleO_sqrtX_Tl P hlam0 hlam1))
    exact this.congr_left fun T => by simp only [hR₁]; ring
  have o2 : R₂ =o[atTop] N := by
    have hclO : cl =O[atTop] (fun _ => (1:ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2 / P.lam + 1 / 3) ?_
      filter_upwards [eventually_clam_bounds P hlam0 hlam1] with T h
      rw [abs_of_nonneg h.1]; exact h.2
    have hK1 : Tendsto (fun T => K T - 1) atTop (𝓝 0) := by simpa using hKto.sub_const 1
    have hKO : K =O[atTop] (fun _ => (1:ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2) ?_
      filter_upwards [hKto.eventually (eventually_ge_nhds (show (0:ℝ) < 1 by norm_num)),
        hKto.eventually (eventually_le_nhds (show (1:ℝ) < 2 by norm_num))] with T h1 h2
      rw [abs_of_nonneg h1]; exact h2
    have i1 : (fun T => (K T - 1) * N T) =o[atTop] N := isLittleO_of_tendsto_zero_mul hK1
    have i2 : (fun T => K T * (|CN| * Real.log T)) =o[atTop] N :=
      isLittleO_of_bdd_mul hKO ((isLittleO_N_of_isLittleO_Tl Z hR isLittleO_log_Tl).const_mul_left _)
    exact isLittleO_of_bdd_mul hclO (i1.add i2)
  -- cl → κ(λ)
  have hclto : Tendsto cl atTop (𝓝 (kfun P.lam)) := by
    have hl1 := ThmD.tendsto_lam1 (P := P) hlam0
    simp only [hcl, kfun]
    exact ((tendsto_const_nhds.div hl1 hlam0.ne')).add (hl1.div_const 3)
  have hNtop : Tendsto N atTop atTop := tendsto_N_atTop Z hR
  refine ⟨fun δ hδ => ?_, fun δ hδ => ?_⟩
  · filter_upwards [hpt, o1.def hδ, hNtop.eventually_ge_atTop 0] with T h h1 hN0
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hN0] at h1
    have := (abs_le.mp h.1).1
    have : R₁ T ≤ δ * N T := (le_abs_self _).trans h1
    simp only [hNdef] at *
    linarith
  · have hδ2 : 0 < δ / 2 := by linarith
    filter_upwards [hpt, o2.def hδ2, hNtop.eventually_ge_atTop 0,
      hclto.eventually (eventually_le_nhds (show kfun P.lam < kfun P.lam + δ / 2 by linarith))]
      with T h h2 hN0 hcl2
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hN0] at h2
    have hR₂ : R₂ T ≤ δ / 2 * N T := (le_abs_self _).trans h2
    have hclN : cl T * N T ≤ (kfun P.lam + δ / 2) * N T := mul_le_mul_of_nonneg_right hcl2 hN0
    simp only [hNdef] at *
    linarith [h.2]

end Moments

/-! ## The multiplicity-aware theorems at fixed λ < 1, abstract zero configuration -/

section Abstract

variable (Z : ZeroConfig) (H : PaperInputs Z) (P : Params) (hP : P.Valid) (hlam : P.lam < 1)
  (hTr : ThmTracesHyp P Z)

include H hP hlam hTr in
/-- **multiplicity-aware Theorem B at fixed λ ∈ (0,1)**: N₀ˢ(T,2T) ≥ (H(λ) − ε)·N(T,2T). -/
theorem thmBmult_abstract :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (Hfun P.lam - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.N0s T (2 * T) := by
  have hlam0 := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hlam.le
  obtain ⟨hGzGp, ha, hNII, -⟩ := eventually_side_conditions Z H P hP
  obtain ⟨θ₀, hTail, Cθ, hθ⟩ := Tail.eventually_tailPackage Z H P hP
  obtain ⟨htrace, hfrob⟩ := moments_of_traces Z H P hP hlam hTr hGzGp ha
  have hLtop := tendsto_L_atTop P hlam0
  have hapos : ∀ᶠ T in atTop, 1 / 2 ≤ P.a T := by
    filter_upwards [ha, hLtop.eventually_ge_atTop (4 * P.w)] with T h hL4
    have hw := hP.one_le_w
    have hLpos : 0 < P.L T := by linarith
    have : 2 * P.w / P.L T ≤ 1 / 2 := by rw [div_le_iff₀ hLpos]; linarith
    linarith [h.1]
  have hwL : ∀ᶠ T in atTop, 8 * P.w ≤ P.L T := hLtop.eventually_ge_atTop _
  -- the c = 2 seam, eventually
  have h0 : ∀ᶠ T in atTop, 4 * rtrace (P.hat T (Z.Gz P T)) - frobSq (P.hat T (Z.Gz P T))
      - 2 * (Z.N T (2 * T) : ℝ) - 3 * (NII Z T : ℝ)
      - θ₀ T / (P.a T * P.L T)
          * (4 + 2 * Real.sqrt (frobSq (P.hat T (Z.Gz P T))) + θ₀ T / (P.a T * P.L T))
      ≤ (Z.N0s T (2 * T) : ℝ) := by
    filter_upwards [hTail, hwL, hapos, eventually_ge_atTop (0:ℝ), eventually_l_pos]
      with T hTl h8 ha2 hT0 hl
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
    exact seamA_mult2 hT0 ZeroSide.phiHatConj ZeroSide.phiHatReal (ZeroSide.poissonSq hP h8) hTl
      (by linarith) hLpos
  have hB0 : ∀ᶠ T in atTop, 0 ≤ θ₀ T / (P.a T * P.L T) := by
    filter_upwards [hTail, hapos, eventually_l_pos] with T hTl ha2 hl
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
    exact div_nonneg hTl.theta_nonneg (by positivity)
  have hBto : Tendsto (fun T => θ₀ T / (P.a T * P.L T)) atTop (𝓝 0) := by
    have hup : Tendsto (fun T => 2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) atTop (𝓝 0) := by
      simpa using (tendsto_theta_over_L P hlam0 hlam1).const_mul (2 * |Cθ|)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup hB0 ?_
    filter_upwards [hTail, hapos, eventually_l_pos, hθ, eventually_gt_atTop (0:ℝ)]
      with T hTl ha2 hl hθT hT0
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
    have hapos' : 0 < P.a T := by linarith
    have hq' : 0 ≤ l T * T ^ (P.lam / 2 - 1) / P.L T := by positivity
    rw [div_le_iff₀ (mul_pos hapos' hLpos)]
    calc θ₀ T ≤ Cθ * l T * T ^ (P.lam / 2 - 1) := hθT
      _ ≤ |Cθ| * l T * T ^ (P.lam / 2 - 1) := by gcongr; exact le_abs_self _
      _ = |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T := by field_simp
      _ ≤ (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (P.a T * P.L T) := by
          have e : |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T
              = (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (1 / 2 * P.L T) := by ring
          rw [e]; gcongr
  have hNII_o : (fun T => (NII Z T : ℝ)) =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) := by
    obtain ⟨CII, hII⟩ := hNII
    have hO : (fun T => (NII Z T : ℝ)) =O[atTop] (fun T => Real.sqrt T * l T) := by
      refine IsBigO.of_bound CII ?_
      filter_upwards [hII, eventually_l_pos] with T h hl
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (by positivity)]
      simpa [mul_assoc] using h
    exact hO.trans_isLittleO (isLittleO_N_of_isLittleO_Tl Z H.RvM isLittleO_sqrt_mul_l_Tl)
  have hNtop := tendsto_N_atTop Z H.RvM
  have h := count_certificate Z P (kfun P.lam) (fun T => (Z.N0s T (2 * T) : ℝ)) θ₀ h0 hB0 hBto
    hNII_o hNtop htrace hfrob
  simpa only [Hfun_eq_two_sub_kfun] using h

include H hP hlam hTr in
/-- **multiplicity-aware Theorem C at fixed λ ∈ (0,1)**: N_d(T,2T) ≥ (G(λ) − ε)·N(T,2T),
G(λ) = 3/2 − κ(λ)/2. -/
theorem thmCmult_abstract :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (Gfun P.lam - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.Nd T (2 * T) := by
  have hlam0 := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hlam.le
  obtain ⟨hGzGp, ha, hNII, -⟩ := eventually_side_conditions Z H P hP
  obtain ⟨θ₀, hTail, Cθ, hθ⟩ := Tail.eventually_tailPackage Z H P hP
  obtain ⟨htrace, hfrob⟩ := moments_of_traces Z H P hP hlam hTr hGzGp ha
  have hLtop := tendsto_L_atTop P hlam0
  have hapos : ∀ᶠ T in atTop, 1 / 2 ≤ P.a T := by
    filter_upwards [ha, hLtop.eventually_ge_atTop (4 * P.w)] with T h hL4
    have hw := hP.one_le_w
    have hLpos : 0 < P.L T := by linarith
    have : 2 * P.w / P.L T ≤ 1 / 2 := by rw [div_le_iff₀ hLpos]; linarith
    linarith [h.1]
  have hwL : ∀ᶠ T in atTop, 8 * P.w ≤ P.L T := hLtop.eventually_ge_atTop _
  have h0 : ∀ᶠ T in atTop, 6 * rtrace (P.hat T (Z.Gz P T)) - frobSq (P.hat T (Z.Gz P T))
      - 3 * (Z.N T (2 * T) : ℝ) - 5 * (NII Z T : ℝ)
      - θ₀ T / (P.a T * P.L T)
          * (6 + 2 * Real.sqrt (frobSq (P.hat T (Z.Gz P T))) + θ₀ T / (P.a T * P.L T))
      ≤ 2 * (Z.Nd T (2 * T) : ℝ) := by
    filter_upwards [hTail, hwL, hapos, eventually_ge_atTop (0:ℝ), eventually_l_pos]
      with T hTl h8 ha2 hT0 hl
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
    exact seamA_mult3 hT0 ZeroSide.phiHatConj ZeroSide.phiHatReal (ZeroSide.poissonSq hP h8) hTl
      (by linarith) hLpos
  have hB0 : ∀ᶠ T in atTop, 0 ≤ θ₀ T / (P.a T * P.L T) := by
    filter_upwards [hTail, hapos, eventually_l_pos] with T hTl ha2 hl
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
    exact div_nonneg hTl.theta_nonneg (by positivity)
  have hBto : Tendsto (fun T => θ₀ T / (P.a T * P.L T)) atTop (𝓝 0) := by
    have hup : Tendsto (fun T => 2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) atTop (𝓝 0) := by
      simpa using (tendsto_theta_over_L P hlam0 hlam1).const_mul (2 * |Cθ|)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup hB0 ?_
    filter_upwards [hTail, hapos, eventually_l_pos, hθ, eventually_gt_atTop (0:ℝ)]
      with T hTl ha2 hl hθT hT0
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
    have hapos' : 0 < P.a T := by linarith
    have hq' : 0 ≤ l T * T ^ (P.lam / 2 - 1) / P.L T := by positivity
    rw [div_le_iff₀ (mul_pos hapos' hLpos)]
    calc θ₀ T ≤ Cθ * l T * T ^ (P.lam / 2 - 1) := hθT
      _ ≤ |Cθ| * l T * T ^ (P.lam / 2 - 1) := by gcongr; exact le_abs_self _
      _ = |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T := by field_simp
      _ ≤ (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (P.a T * P.L T) := by
          have e : |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T
              = (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (1 / 2 * P.L T) := by ring
          rw [e]; gcongr
  have hNII_o : (fun T => (NII Z T : ℝ)) =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) := by
    obtain ⟨CII, hII⟩ := hNII
    have hO : (fun T => (NII Z T : ℝ)) =O[atTop] (fun T => Real.sqrt T * l T) := by
      refine IsBigO.of_bound CII ?_
      filter_upwards [hII, eventually_l_pos] with T h hl
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (by positivity)]
      simpa [mul_assoc] using h
    exact hO.trans_isLittleO (isLittleO_N_of_isLittleO_Tl Z H.RvM isLittleO_sqrt_mul_l_Tl)
  have hNtop := tendsto_N_atTop Z H.RvM
  have h := count_certificate_c3 Z P (kfun P.lam) (fun T => (Z.Nd T (2 * T) : ℝ)) θ₀ h0 hB0 hBto
    hNII_o hNtop htrace hfrob
  simpa only [Gfun] using h

end Abstract

/-! ## ζ: fixed λ, then λ → 1⁻, then cumulative — NO hypotheses -/

section Zeta

/-- **multiplicity-aware Theorem B for ζ at fixed λ ∈ (0,1), UNCONDITIONAL**:
(H(λ) − ε)·N(T,2T) ≤ N₀ˢ(T,2T). -/
theorem thmB_mult_lam {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Hfun lam - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by
  have hP := paramsOf_valid taperProfile_stdProfile h0 h1.le
  exact thmBmult_abstract zetaZeroConfig paperInputs_zeta (paramsOf stdProfile lam) hP h1
    (PrimeSide.thm_traces hP paperInputs_zeta)

/-- **multiplicity-aware Theorem C for ζ at fixed λ ∈ (0,1), UNCONDITIONAL**:
(G(λ) − ε)·N(T,2T) ≤ N_d(T,2T), G(λ) = 3/2 − 1/(2λ) − λ/6. -/
theorem thmC_mult_lam {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Gfun lam - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) := by
  have hP := paramsOf_valid taperProfile_stdProfile h0 h1.le
  exact thmCmult_abstract zetaZeroConfig paperInputs_zeta (paramsOf stdProfile lam) hP h1
    (PrimeSide.thm_traces hP paperInputs_zeta)

/-- **At least 2/3 of the zeros of ζ are SIMPLE AND ON THE CRITICAL LINE, UNCONDITIONAL**
(this is the paper's [thm:B]; Zeta23/Final.lean has the Cauchy–Schwarz form with 1/2): for every ε > 0 and all large T,
(2/3 − ε)·N(T,2T) ≤ N₀ˢ(T,2T), for Mathlib's riemannZeta. -/
theorem thmB₀_mult :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) :=
  eps_form_twoThirds (N := fun T => (Ncount T (2 * T) : ℝ))
    (lower := fun T => (N0simple T (2 * T) : ℝ)) (fun _ => Nat.cast_nonneg _)
    fun lam hl1 hl2 => thmB_mult_lam (by linarith) hl2

/-- **At least 5/6 of the zeros of ζ are DISTINCT, UNCONDITIONAL** (the paper's [thm:C];
Zeta23/Final.lean has the Cauchy–Schwarz form with 3/4): (5/6 − ε)·N(T,2T) ≤ N_d(T,2T). -/
theorem thmC₀_mult :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (5 / 6 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T) :=
  eps_form_fiveSixths (N := fun T => (Ncount T (2 * T) : ℝ))
    (lower := fun T => (Ndist T (2 * T) : ℝ)) (fun _ => Nat.cast_nonneg _)
    fun lam hl1 hl2 => thmC_mult_lam (by linarith) hl2

/-- cumulative form: liminf N₀ˢ(T)/N(T) ≥ 2/3. -/
theorem thmB₀_mult_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount 0 T : ℝ) ≤ N0simple 0 T :=
  cumulative_of_dyadic zetaSeam paperInputs_zeta.RvM (fun _ _ _ => N0simple_add' zetaSeam) thmB₀_mult

/-- cumulative form: liminf N_d(T)/N(T) ≥ 5/6. -/
theorem thmC₀_mult_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (5 / 6 - ε) * (Ncount 0 T : ℝ) ≤ Ndist 0 T :=
  cumulative_of_dyadic zetaSeam paperInputs_zeta.RvM (fun _ _ _ => Ndist_add' zetaSeam) thmC₀_mult

end Zeta

end Zeta23

end
