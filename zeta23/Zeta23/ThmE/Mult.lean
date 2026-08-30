/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmE/Mult.lean — the multiplicity-aware Theorem E ([thm:E] with the paper's stated constants):
for every primitive Dirichlet character χ mod q > 1 and Mathlib's 'DirichletCharacter.LFunction χ',
NO hypotheses: at least (2/3 − ε)·N_χ(T,2T) of the zeros are SIMPLE AND on the critical line and at
least (5/6 − ε)·N_χ(T,2T) are DISTINCT (the Cauchy–Schwarz forms in Zeta23/ThmE/Final.lean give 1/2
and 3/4); fixed-λ forms with H(λ), G(λ).  This is Zeta23/FinalMult.lean's moments/certificate
argument with the χ-scalars (ℓ_{1,χ}, λ_{1,χ}, ν_{X,χ}) of Zeta23/ThmE/AssemblyQ.lean.  The
multiplicity-aware zero side, seams and certificates are ZeroSide/Mult.lean, Assembly/SeamMult.lean
and Assembly/Certificate*.lean.
-/
import Zeta23.FinalMult
import Zeta23.ThmE.Final
import Zeta23.ThmDE.Limit

noncomputable section

open Filter Asymptotics Topology Real RHLinalg

namespace Zeta23
namespace ThmE

open Assembly

section Moments

variable (Z : ZeroConfig) (κ : ℕ) {q : ℕ} (hq : 1 ≤ q) (cf : ℕ → ℂ) (hRvM : RiemannVonMangoldtChi q Z) (P : Params) (hP : P.Valid) (hlam : P.lam < 1)
  (hTr : ThmTracesHypChi P κ q cf Z)
  (hGzGp : ∀ᶠ T in atTop, Z.Gz P T = GpChi P κ q cf T)
  (ha : ∀ᶠ T in atTop, 1 - 2 * P.w / P.L T ≤ P.a T ∧ P.a T ≤ 1)

include hq hRvM hP hlam hTr hGzGp ha in
/-- [thm:traces] + H-RvM ⟹ the two moment hypotheses of the certificate with κ = κ(λ):
tr Ĝ ≥ (1 − δ)N and ‖Ĝ‖_F² ≤ (κ(λ) + δ)N eventually, for every δ > 0. -/
theorem moments_of_traces_chi :
    (∀ δ > (0:ℝ), ∀ᶠ T in atTop, (1 - δ) * (Z.N T (2 * T) : ℝ) ≤ rtrace (P.hat T (Z.Gz P T))) ∧
    (∀ δ > (0:ℝ), ∀ᶠ T in atTop,
      frobSq (P.hat T (Z.Gz P T)) ≤ (kfun P.lam + δ) * (Z.N T (2 * T) : ℝ)) := by
  have hlam0 := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hlam.le
  have hw0 : 0 ≤ P.w := zero_le_one.trans hP.one_le_w
  have hcalE := calE_tendsto_zero P hlam0 hlam1 hw0
  obtain ⟨C₁, hC₁, T₁, htr1⟩ := hTr.tr1
  obtain ⟨C₂, hC₂, T₂, htr2⟩ := hTr.tr2
  obtain ⟨CN, T₃, hRvM'⟩ := hRvM.main
  set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hNdef
  set cl : ℝ → ℝ := fun T => 1 / lam1q P q T + lam1q P q T / 3 with hcl
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
    have hℓ₁ : 0 < ell1q q T := ell1q_pos hq hT0 hl
    have hKnn : 0 ≤ 1 + C₂ * P.calE T := by linarith
    have htr2' : trGtildeSqChi P κ q cf T - mainTr2Chi P q T
        ≤ C₂ * P.calE T * mainTr2Chi P q T := by
      have := htr2 T hT₂
      simp only at this
      rw [← mul_assoc] at this
      exact (le_abs_self _).trans this
    have htr1' : |trGtildeChi P κ q cf T - P.a T * P.L T * (Z.N T (2 * T) : ℝ)|
        ≤ C₁ * (P.L T * Real.sqrt (P.X T)) := by
      have := htr1 T hT₁; simpa only using this
    have hRvM'' : T * ell1q q T / (2 * Real.pi) ≤ N T + |CN| * Real.log T := by
      have h1 := (abs_le.mp (hRvM' T hT₃)).1
      have h2 : CN * Real.log T ≤ |CN| * Real.log T :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hlog
      have h3 : T / (2 * Real.pi) * ell1q q T = T * ell1q q T / (2 * Real.pi) := by ring
      simp only [hNdef]; linarith
    have hSB := seamBChi P κ q cf hGG hapos' hLpos hℓ₁ htr1' hKnn htr2' hRvM''
    refine ⟨?_, ?_⟩
    · simpa only [hR₁, hNdef] using hSB.1
    · have := hSB.2
      simp only [hR₂, hcl, hK, hNdef] at this ⊢
      linarith
  -- R₁, R₂ = o(N)  (as in Assembly.thmA_abstract_err)
  have o1 : R₁ =o[atTop] N := by
    have hbd : (fun T => C₁ / P.a T) =O[atTop] (fun _ => (1:ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2 * C₁) ?_
      filter_upwards [hapos] with T ha2
      rw [abs_of_nonneg (div_nonneg hC₁.le (by linarith))]
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have := isLittleO_of_bdd_mul hbd
      (isLittleO_N_of_isLittleO_Tl_chi q Z hq hRvM (isLittleO_sqrtX_Tl P hlam0 hlam1))
    exact this.congr_left fun T => by simp only [hR₁]; ring
  have o2 : R₂ =o[atTop] N := by
    have hclO : cl =O[atTop] (fun _ => (1:ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2 / P.lam + 1 / 3) ?_
      filter_upwards [eventually_clam_bounds_chi q P hq hlam0 hlam1] with T h
      rw [abs_of_nonneg h.1]; exact h.2
    have hK1 : Tendsto (fun T => K T - 1) atTop (𝓝 0) := by simpa using hKto.sub_const 1
    have hKO : K =O[atTop] (fun _ => (1:ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2) ?_
      filter_upwards [hKto.eventually (eventually_ge_nhds (show (0:ℝ) < 1 by norm_num)),
        hKto.eventually (eventually_le_nhds (show (1:ℝ) < 2 by norm_num))] with T h1 h2
      rw [abs_of_nonneg h1]; exact h2
    have i1 : (fun T => (K T - 1) * N T) =o[atTop] N := isLittleO_of_tendsto_zero_mul hK1
    have i2 : (fun T => K T * (|CN| * Real.log T)) =o[atTop] N :=
      isLittleO_of_bdd_mul hKO ((isLittleO_N_of_isLittleO_Tl_chi q Z hq hRvM isLittleO_log_Tl).const_mul_left _)
    exact isLittleO_of_bdd_mul hclO (i1.add i2)
  -- cl → κ(λ)
  have hclto : Tendsto cl atTop (𝓝 (kfun P.lam)) := by
    have hl1 := ThmDE.tendsto_lam1q (P := P) hP hq
    simp only [hcl, kfun]
    exact ((tendsto_const_nhds.div hl1 hlam0.ne')).add (hl1.div_const 3)
  have hNtop : Tendsto N atTop atTop := tendsto_N_atTop_chi q Z hq hRvM
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

section Abstract

variable (Z : ZeroConfig) (κ : ℕ) {q : ℕ} (hq : 1 ≤ q) (cf : ℕ → ℂ) (hRvM : RiemannVonMangoldtChi q Z) (P : Params) (hP : P.Valid) (hlam : P.lam < 1)
  (hTr : ThmTracesHypChi P κ q cf Z)
  (hGzGp : ∀ᶠ T in atTop, Z.Gz P T = GpChi P κ q cf T)

include hq hRvM hP hlam hTr hGzGp in
/-- **multiplicity-aware Theorem B at fixed λ ∈ (0,1)**: N₀ˢ(T,2T) ≥ (H(λ) − ε)·N(T,2T). -/
theorem thmBmult_chi_abstract :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (Hfun P.lam - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.N0s T (2 * T) := by
  have hlam0 := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hlam.le
  obtain ⟨θ₀, hTail, Cθ, hθ⟩ := tailPackageChi Z hRvM P hP
  obtain ⟨CII, hII⟩ := NIIChi Z hRvM
  have ha : ∀ᶠ T in atTop, 1 - 2 * P.w / P.L T ≤ P.a T ∧ P.a T ≤ 1 := by
    filter_upwards [(Tail.tendsto_L_atTop _ hP).eventually_ge_atTop (8 * P.w)] with T hwL
    exact ⟨(Params.one_sub_le_b hP hwL).trans (Params.b_le_a hP hwL), Params.a_le_one hP hwL⟩
  obtain ⟨htrace, hfrob⟩ := moments_of_traces_chi Z κ hq cf hRvM P hP hlam hTr hGzGp ha
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
    have hO : (fun T => (NII Z T : ℝ)) =O[atTop] (fun T => Real.sqrt T * l T) := by
      refine IsBigO.of_bound CII ?_
      filter_upwards [hII, eventually_l_pos] with T h hl
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (by positivity)]
      simpa [mul_assoc] using h
    exact hO.trans_isLittleO (isLittleO_N_of_isLittleO_Tl_chi q Z hq hRvM isLittleO_sqrt_mul_l_Tl)
  have hNtop := tendsto_N_atTop_chi q Z hq hRvM
  have h := count_certificate Z P (kfun P.lam) (fun T => (Z.N0s T (2 * T) : ℝ)) θ₀ h0 hB0 hBto
    hNII_o hNtop htrace hfrob
  simpa only [Hfun_eq_two_sub_kfun] using h

include hq hRvM hP hlam hTr hGzGp in
/-- **multiplicity-aware Theorem C at fixed λ ∈ (0,1)**: N_d(T,2T) ≥ (G(λ) − ε)·N(T,2T),
G(λ) = 3/2 − κ(λ)/2. -/
theorem thmCmult_chi_abstract :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (Gfun P.lam - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.Nd T (2 * T) := by
  have hlam0 := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hlam.le
  obtain ⟨θ₀, hTail, Cθ, hθ⟩ := tailPackageChi Z hRvM P hP
  obtain ⟨CII, hII⟩ := NIIChi Z hRvM
  have ha : ∀ᶠ T in atTop, 1 - 2 * P.w / P.L T ≤ P.a T ∧ P.a T ≤ 1 := by
    filter_upwards [(Tail.tendsto_L_atTop _ hP).eventually_ge_atTop (8 * P.w)] with T hwL
    exact ⟨(Params.one_sub_le_b hP hwL).trans (Params.b_le_a hP hwL), Params.a_le_one hP hwL⟩
  obtain ⟨htrace, hfrob⟩ := moments_of_traces_chi Z κ hq cf hRvM P hP hlam hTr hGzGp ha
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
    have hO : (fun T => (NII Z T : ℝ)) =O[atTop] (fun T => Real.sqrt T * l T) := by
      refine IsBigO.of_bound CII ?_
      filter_upwards [hII, eventually_l_pos] with T h hl
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (by positivity)]
      simpa [mul_assoc] using h
    exact hO.trans_isLittleO (isLittleO_N_of_isLittleO_Tl_chi q Z hq hRvM isLittleO_sqrt_mul_l_Tl)
  have hNtop := tendsto_N_atTop_chi q Z hq hRvM
  have h := count_certificate_c3 Z P (kfun P.lam) (fun T => (Z.Nd T (2 * T) : ℝ)) θ₀ h0 hB0 hBto
    hNII_o hNtop htrace hfrob
  simpa only [Gfun] using h

end Abstract

/-! ## L(s,χ): fixed λ, then λ → 1⁻ — NO hypotheses -/

section Dirichlet

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- multiplicity-aware Theorem E/B at fixed λ ∈ (0,1): (H(λ) − ε)·N_χ ≤ N^s_{0,χ}, UNCONDITIONAL. -/
theorem thmE_B_mult_lam (hq : 1 < q) (hprim : χ.IsPrimitive) {lam : ℝ} (h0 : 0 < lam)
    (h1 : lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Hfun lam - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0simpleL χ T (2 * T) := by
  have hP := paramsOf_valid taperProfile_stdProfile h0 h1.le
  have H := paperInputsChi_L hq hprim
  have hTr := thm_traces_chi hP (by omega) (coeffUnimodular_of_primitive hq hprim) H
    (PrimeSide.localHypsEventually hP)
  have hGzGp := eventually_GzGpChi _ hP H.EF
  simpa [paramsOf] using thmBmult_chi_abstract (LZeros (LSeam_of hq hprim)) (parity χ) (by omega) (coeff χ)
    H.RvM (paramsOf stdProfile lam) hP h1 hTr hGzGp

/-- multiplicity-aware Theorem E/C at fixed λ ∈ (0,1): (G(λ) − ε)·N_χ ≤ N_{d,χ}, UNCONDITIONAL. -/
theorem thmE_C_mult_lam (hq : 1 < q) (hprim : χ.IsPrimitive) {lam : ℝ} (h0 : 0 < lam)
    (h1 : lam < 1) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Gfun lam - ε) * (NcountL χ T (2 * T) : ℝ) ≤ NdistL χ T (2 * T) := by
  have hP := paramsOf_valid taperProfile_stdProfile h0 h1.le
  have H := paperInputsChi_L hq hprim
  have hTr := thm_traces_chi hP (by omega) (coeffUnimodular_of_primitive hq hprim) H
    (PrimeSide.localHypsEventually hP)
  have hGzGp := eventually_GzGpChi _ hP H.EF
  simpa [paramsOf] using thmCmult_chi_abstract (LZeros (LSeam_of hq hprim)) (parity χ) (by omega) (coeff χ)
    H.RvM (paramsOf stdProfile lam) hP h1 hTr hGzGp

/-- **At least 2/3 of the zeros of L(s,χ) are SIMPLE AND ON THE CRITICAL LINE, UNCONDITIONAL**
(every primitive χ mod q > 1; as stated in [thm:E]). -/
theorem thmE_B₀_mult (hq : 1 < q) (hprim : χ.IsPrimitive) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 / 3 - ε) * (NcountL χ T (2 * T) : ℝ) ≤ N0simpleL χ T (2 * T) :=
  eps_form_twoThirds (N := fun T => (NcountL χ T (2 * T) : ℝ))
    (lower := fun T => (N0simpleL χ T (2 * T) : ℝ)) (fun _ => Nat.cast_nonneg _)
    fun lam hl1 hl2 => thmE_B_mult_lam hq hprim (by linarith) hl2

/-- **At least 5/6 of the zeros of L(s,χ) are DISTINCT, UNCONDITIONAL** (every primitive χ mod
q > 1; as stated in [thm:E]). -/
theorem thmE_C₀_mult (hq : 1 < q) (hprim : χ.IsPrimitive) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (5 / 6 - ε) * (NcountL χ T (2 * T) : ℝ) ≤ NdistL χ T (2 * T) :=
  eps_form_fiveSixths (N := fun T => (NcountL χ T (2 * T) : ℝ))
    (lower := fun T => (NdistL χ T (2 * T) : ℝ)) (fun _ => Nat.cast_nonneg _)
    fun lam hl1 hl2 => thmE_C_mult_lam hq hprim (by linarith) hl2

end Dirichlet

end ThmE
end Zeta23

end
