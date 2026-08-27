/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Assembly.lean — composing the ξ′ interface propositions into the fixed-λ theorem.
See Zeta23/XiPrime/Statement.lean for the Props.

  §A1  CoeffMoments ∧ XiTraceTransfer ⟹ GzMoments            (pure eventually-algebra)
  §A2  GzMoments (flat family Pf := fun _ => P) + H-RvM for Z ⟹ the two fixed-λ certificate bounds
       (2 − κ − ε)N ≤ N₀ˢ and (3/2 − κ/2 − ε)N ≤ N_d, for an ABSTRACT Z : ZeroConfig — a copy of
       Zeta23.FinalMult.thmBmult_abstract / thmCmult_abstract with (i) the moments taken as the hypothesis
       GzMoments instead of being derived from ThmTracesHyp + H-EF, and (ii) PaperInputs replaced by the one
       field actually used on the zero side, RiemannVonMangoldt Z (local count ⟹ prop:tail package and NII;
       main ⟹ N → ∞ and the o(N) calculus).  The zero side (BlockInputs, TailInputs, seamA_mult2/3,
       count_certificate, count_certificate_c3) is the tree's, verbatim, generic in Z.
  §A3  The analogue for a height family Pf (e.g. P.atV v), via the Pf-generic (function-abstract)
       count_certificate of CertificateFn, whose proof only ever touches the two real numbers
       rtrace/frobSq of Ĝ(T).
-/
import Zeta23.XiPrime.Statement
import Zeta23.XiPrime.CertificateFn
import Zeta23.FinalMult

noncomputable section

open Filter Asymptotics Topology Real RHLinalg

namespace Zeta23
namespace XiPrime

open Assembly

/-! ## §A1. moments of M̂ᵀ + trace transfer ⟹ moments of Ĝ¹ -/

theorem gzMoments_of_transfer (Z : ZeroConfig) (Pf : ℝ → Params) (F : CoeffFamily) {κ : ℝ}
    (hκ : 0 ≤ κ) (hCM : CoeffMoments Z Pf F κ) (hTT : XiTraceTransfer Z Pf F) :
    GzMoments Z Pf κ := by
  obtain ⟨hMtr, hMfr⟩ := hCM
  obtain ⟨hTtr, hTfr⟩ := hTT
  refine ⟨fun δ hδ => ?_, fun δ hδ => ?_⟩
  · have hδ2 : 0 < δ / 2 := by linarith
    filter_upwards [hMtr (δ / 2) hδ2, hTtr (δ / 2) hδ2] with T hM hT
    have h1 := hM.1
    have h2 := (abs_le.mp hT).1
    linarith
  · -- choose η with (1+η)(κ+η) + η ≤ κ + δ: η := min 1 (δ / (κ + 3)) works since
    -- (1+η)(κ+η)+η = κ + η(κ + 1 + η) + η ≤ κ + η(κ+3) for η ≤ 1.
    set η : ℝ := min 1 (δ / (κ + 3)) with hη
    have hη0 : 0 < η := lt_min zero_lt_one (div_pos hδ (by linarith))
    have hη1 : η ≤ 1 := min_le_left _ _
    have hηδ : η * (κ + 3) ≤ δ := by
      have : η ≤ δ / (κ + 3) := min_le_right _ _
      rwa [le_div_iff₀ (by linarith)] at this
    filter_upwards [hMfr η hη0, hTfr η hη0, hMtr 1 zero_lt_one] with T hM hT hpos
    have hN0 : 0 ≤ (Z.N T (2 * T) : ℝ) := Nat.cast_nonneg _
    have hfrM0 : 0 ≤ frobSq ((Pf T).hat T ((Pf T).GpC T (F.c T))) := frobSq_nonneg _
    calc frobSq ((Pf T).hat T (Z.Gz (Pf T) T))
        ≤ (1 + η) * frobSq ((Pf T).hat T ((Pf T).GpC T (F.c T))) + η * (Z.N T (2 * T) : ℝ) := hT
      _ ≤ (1 + η) * ((κ + η) * (Z.N T (2 * T) : ℝ)) + η * (Z.N T (2 * T) : ℝ) := by
          gcongr
      _ = (κ + (η * (κ + 1 + η) + η)) * (Z.N T (2 * T) : ℝ) := by ring
      _ ≤ (κ + δ) * (Z.N T (2 * T) : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ hN0
          nlinarith

/-- κ in CoeffMoments is automatically ≥ 0: ‖M̂ᵀ‖_F² ≥ 0 and N(T,2T) → ∞ (H-RvM), so (κ+δ)N ≥ 0 for
every δ > 0 at some large T.  (Removes the "0 ≤ κ" side input of gzMoments_of_transfer downstream.) -/
theorem kappa_nonneg_of_coeffMoments (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) (Pf : ℝ → Params)
    (F : CoeffFamily) {κ : ℝ} (hCM : CoeffMoments Z Pf F κ) : 0 ≤ κ := by
  rcases le_or_gt 0 κ with h | hneg
  · exact h
  · exfalso
    obtain ⟨-, hfr⟩ := hCM
    have hδ : 0 < -κ / 2 := by linarith
    have hN := (tendsto_N_atTop Z hR).eventually_gt_atTop 0
    obtain ⟨T, hT, hNT⟩ := ((hfr (-κ / 2) hδ).and hN).exists
    have h0 := frobSq_nonneg ((Pf T).hat T ((Pf T).GpC T (F.c T)))
    have : (κ + -κ / 2) * (Z.N T (2 * T) : ℝ) < 0 := by
      have hk : κ + -κ / 2 < 0 := by linarith
      exact mul_neg_of_neg_of_pos hk hNT
    linarith

/-- same for GzMoments. -/
theorem kappa_nonneg_of_gzMoments (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) (Pf : ℝ → Params)
    {κ : ℝ} (hM : GzMoments Z Pf κ) : 0 ≤ κ := by
  rcases le_or_gt 0 κ with h | hneg
  · exact h
  · exfalso
    obtain ⟨-, hfr⟩ := hM
    have hδ : 0 < -κ / 2 := by linarith
    have hN := (tendsto_N_atTop Z hR).eventually_gt_atTop 0
    obtain ⟨T, hT, hNT⟩ := ((hfr (-κ / 2) hδ).and hN).exists
    have h0 := frobSq_nonneg ((Pf T).hat T (Z.Gz (Pf T) T))
    have : (κ + -κ / 2) * (Z.N T (2 * T) : ℝ) < 0 := by
      have hk : κ + -κ / 2 < 0 := by linarith
      exact mul_neg_of_neg_of_pos hk hNT
    linarith

/-! ## §A2. The fixed-λ certificate bounds from GzMoments, flat family, abstract Z -/

section Flat

variable (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) (P : Params) (hP : P.Valid) (hlam : P.lam < 1)

include hR hP in
/-- prop:tail package for Z from the LOCAL COUNT alone (Zeta23.Tail.eventually_tailPackage takes the whole
PaperInputs bundle but uses only RvM.local_count; this is that proof with the bundle opened). -/
theorem eventually_tailPackage_of_rvm :
    ∃ θ₀ : ℝ → ℝ, (∀ᶠ T in atTop, Assembly.TailInputs Z P T (θ₀ T)) ∧
      ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1) := by
  obtain ⟨A₀, hA₀, hloc⟩ := hR.local_count
  have hwL : ∀ᶠ T in atTop, 8 * P.w ≤ P.L T := (tendsto_L_atTop P hP.lam_pos).eventually_ge_atTop _
  refine ⟨fun T => Tail.theta0 A₀ (Real.exp (P.L T / 4) * P.C1 T) T, ?_, ?_⟩
  · refine Tail.eventually_tailInputs Z P hP hA₀ hloc (fun T => P.C1 T) (fun T => Tail.C1_nonneg P T)
      ?_ ?_ ?_
    · filter_upwards [hwL] with T hwL
      exact fun r y hy hz => Params.norm_phiHat_sub_I_mul_le hP hwL r y hy hz
    · filter_upwards [hwL] with T hwL
      linarith [Params.half_le_a hP hwL]
    · exact Eventually.of_forall fun T z => GzGp.phiHat_conj P T z
  · exact Tail.eventually_theta0_le P hP hA₀ (fun T => P.C1 T) (fun T => Tail.C1_nonneg P T)
      (hwL.mono fun T hwL => Params.C1_le hP hwL)

include hR hP in
/-- the two zero-side side conditions the endgame needs, from RvM.local_count and the taper facts. -/
theorem eventually_side_conditions_of_rvm :
    (∀ᶠ T in atTop, 1 - 2 * P.w / P.L T ≤ P.a T ∧ P.a T ≤ 1) ∧
    (∃ C : ℝ, ∀ᶠ T in atTop, (NII Z T : ℝ) ≤ C * Real.sqrt T * l T) := by
  have hwL : ∀ᶠ T in atTop, 8 * P.w ≤ P.L T := (tendsto_L_atTop P hP.lam_pos).eventually_ge_atTop _
  refine ⟨?_, ?_⟩
  · filter_upwards [hwL] with T hwL
    exact ⟨(Params.one_sub_le_b hP hwL).trans (Params.b_le_a hP hwL), Params.a_le_one hP hwL⟩
  · obtain ⟨A₀, hA₀, hloc⟩ := hR.local_count
    exact Tail.eventually_NII_le Z hA₀ hloc

include hR hP hlam in
/-- **(2 − κ − ε)·N(T,2T) ≤ N₀ˢ(T,2T)** at fixed λ ∈ (0,1), flat window, abstract Z, from GzMoments. -/
theorem simple_bound_of_gzMoments {κ : ℝ} (hM : GzMoments Z (fun _ => P) κ) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 - κ - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.N0s T (2 * T) := by
  have hlam0 := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hlam.le
  obtain ⟨ha, hNII⟩ := eventually_side_conditions_of_rvm Z hR P hP
  obtain ⟨θ₀, hTail, Cθ, hθ⟩ := eventually_tailPackage_of_rvm Z hR P hP
  obtain ⟨htrace, hfrob⟩ := hM
  have hLtop := tendsto_L_atTop P hlam0
  have hapos : ∀ᶠ T in atTop, 1 / 2 ≤ P.a T := by
    filter_upwards [ha, hLtop.eventually_ge_atTop (4 * P.w)] with T h hL4
    have hw := hP.one_le_w
    have hLpos : 0 < P.L T := by linarith
    have : 2 * P.w / P.L T ≤ 1 / 2 := by rw [div_le_iff₀ hLpos]; linarith
    linarith [h.1]
  have hwL : ∀ᶠ T in atTop, 8 * P.w ≤ P.L T := hLtop.eventually_ge_atTop _
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
    exact hO.trans_isLittleO (isLittleO_N_of_isLittleO_Tl Z hR isLittleO_sqrt_mul_l_Tl)
  have hNtop := tendsto_N_atTop Z hR
  exact count_certificate Z P κ (fun T => (Z.N0s T (2 * T) : ℝ)) θ₀ h0 hB0 hBto
    hNII_o hNtop htrace hfrob

include hR hP hlam in
/-- **(3/2 − κ/2 − ε)·N(T,2T) ≤ N_d(T,2T)** at fixed λ ∈ (0,1), flat window, abstract Z, from GzMoments. -/
theorem dist_bound_of_gzMoments {κ : ℝ} (hM : GzMoments Z (fun _ => P) κ) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 2 - κ / 2 - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.Nd T (2 * T) := by
  have hlam0 := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hlam.le
  obtain ⟨ha, hNII⟩ := eventually_side_conditions_of_rvm Z hR P hP
  obtain ⟨θ₀, hTail, Cθ, hθ⟩ := eventually_tailPackage_of_rvm Z hR P hP
  obtain ⟨htrace, hfrob⟩ := hM
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
    exact hO.trans_isLittleO (isLittleO_N_of_isLittleO_Tl Z hR isLittleO_sqrt_mul_l_Tl)
  have hNtop := tendsto_N_atTop Z hR
  exact count_certificate_c3 Z P κ (fun T => (Z.Nd T (2 * T) : ℝ)) θ₀ h0 hB0 hBto
    hNII_o hNtop htrace hfrob

end Flat

/-! ## §A3. The fixed-λ certificate bounds from GzMoments for a HEIGHT FAMILY Pf (quartic window etc.)

The window at height T is (Pf T).phi T (Defs.Params.atV realises a profile v on the taper).  The zero side
is consumed per height exactly as in §A2, through the three facts below (pattern:
Zeta23/ThmD/ZeroSideD.lean for P.atD), and the certificate algebra is CertificateFn's function-abstract copy. -/

/-- **The zero-side facts for a height-indexed window family** that the c = 2, 3 seams consume at heights
T → ∞ (the instance for Pf := P.atV vQuartic is built in XiPrime/QuarticWindow.lean from an
Zeta23.AdmWindow instance for φ_v := √(v(u/L))·φ, as ZeroSideD does for φ_D):
  lam_eq, w_eq — the family shares λ and w (hence L, X, d, τ_k) with P;
  poisson      — lem:poisson ★ for the window at height T (ZeroSide.PoissonSq T (Pf T));
  tail         — the prop:tail package for (Pf T) at height T with the standard rate θ₀ ≤ C·l·T^{λ/2−1}
                 (from RvM.local_count of Z and the decay ‖φ̂_v(r−iy)‖ ≤ e^{L/4}‖φ_v″‖₁/|r−iy|², as
                 Tail.TailHyp.tailInputs / ZeroSideD.eventually_tailPackageD);
  a_half       — a(T) = (1/L)∫φ_v² ≥ 1/2 eventually (v ≥ 27/40 on the window suffices for vQuartic). -/
structure WindowZeroSide (Z : ZeroConfig) (P : Params) (Pf : ℝ → Params) : Prop where
  lam_eq : ∀ T, (Pf T).lam = P.lam
  w_eq : ∀ T, (Pf T).w = P.w
  poisson : ∀ᶠ T in atTop, ZeroSide.PoissonSq T (Pf T)
  tail : ∃ θ₀ : ℝ → ℝ, (∀ᶠ T in atTop, Assembly.TailInputs Z (Pf T) T (θ₀ T)) ∧
    ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1)
  a_half : ∀ᶠ T in atTop, 1 / 2 ≤ (Pf T).a T

/-- the flat family fun _ => P satisfies WindowZeroSide (so §A2 is the special case). -/
theorem windowZeroSide_flat (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) (P : Params) (hP : P.Valid) :
    WindowZeroSide Z P (fun _ => P) := by
  have hLtop := tendsto_L_atTop P hP.lam_pos
  have hwL : ∀ᶠ T in atTop, 8 * P.w ≤ P.L T := hLtop.eventually_ge_atTop _
  obtain ⟨ha, -⟩ := eventually_side_conditions_of_rvm Z hR P hP
  refine ⟨fun _ => rfl, fun _ => rfl, ?_, eventually_tailPackage_of_rvm Z hR P hP, ?_⟩
  · filter_upwards [hwL] with T h8
    exact ZeroSide.poissonSq hP h8
  · filter_upwards [ha, hLtop.eventually_ge_atTop (4 * P.w)] with T h hL4
    have hw := hP.one_le_w
    have hLpos : 0 < P.L T := by linarith
    have : 2 * P.w / P.L T ≤ 1 / 2 := by rw [div_le_iff₀ hLpos]; linarith
    linarith [h.1]

section Family

variable (Z : ZeroConfig) (hR : RiemannVonMangoldt Z) (P : Params) (hP : P.Valid) (hlam : P.lam < 1)
  {Pf : ℝ → Params} (hW : WindowZeroSide Z P Pf)

include hP hlam hW in
/-- the common o(1) bookkeeping for the tail size B(T) := θ₀(T)/(a(T)L(T)) of a family. -/
theorem family_tail_package :
    ∃ θ₀ : ℝ → ℝ, (∀ᶠ T in atTop, Assembly.TailInputs Z (Pf T) T (θ₀ T)) ∧
      (∀ᶠ T in atTop, 0 ≤ θ₀ T / ((Pf T).a T * (Pf T).L T)) ∧
      Tendsto (fun T => θ₀ T / ((Pf T).a T * (Pf T).L T)) atTop (𝓝 0) := by
  have hlam0 := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hlam.le
  have hL : ∀ T, (Pf T).L T = P.L T := fun T => by simp only [Params.L, hW.lam_eq]
  obtain ⟨θ₀, hTail, Cθ, hθ⟩ := hW.tail
  have hLtop := tendsto_L_atTop P hlam0
  have hapos := hW.a_half
  refine ⟨θ₀, hTail, ?_, ?_⟩
  · filter_upwards [hTail, hapos, hLtop.eventually_gt_atTop 0] with T hTl ha2 hLT
    have hLpos : 0 < (Pf T).L T := by rw [hL]; exact hLT
    exact div_nonneg hTl.theta_nonneg (by positivity)
  · have hup : Tendsto (fun T => 2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) atTop (𝓝 0) := by
      simpa using (tendsto_theta_over_L P hlam0 hlam1).const_mul (2 * |Cθ|)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hTail, hapos, hLtop.eventually_gt_atTop 0] with T hTl ha2 hLT
      have hLpos : 0 < (Pf T).L T := by rw [hL]; exact hLT
      exact div_nonneg hTl.theta_nonneg (by positivity)
    · filter_upwards [hTail, hapos, eventually_l_pos, hθ, eventually_gt_atTop (0:ℝ),
        hLtop.eventually_gt_atTop 0] with T hTl ha2 hl hθT hT0 hLT
      rw [hL]
      have hapos' : 0 < (Pf T).a T := by linarith
      have hq' : 0 ≤ l T * T ^ (P.lam / 2 - 1) / P.L T := by positivity
      rw [div_le_iff₀ (mul_pos hapos' hLT)]
      calc θ₀ T ≤ Cθ * l T * T ^ (P.lam / 2 - 1) := hθT
        _ ≤ |Cθ| * l T * T ^ (P.lam / 2 - 1) := by gcongr; exact le_abs_self _
        _ = |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T := by field_simp
        _ ≤ (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * ((Pf T).a T * P.L T) := by
            have e : |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T
                = (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (1 / 2 * P.L T) := by ring
            rw [e]; gcongr

include hR hP hlam hW in
/-- **(2 − κ − ε)·N(T,2T) ≤ N₀ˢ(T,2T)** at fixed λ ∈ (0,1) for a window FAMILY, abstract Z, from GzMoments. -/
theorem simple_bound_of_gzMoments_family {κ : ℝ} (hM : GzMoments Z Pf κ) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 - κ - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.N0s T (2 * T) := by
  have hL : ∀ T, (Pf T).L T = P.L T := fun T => by simp only [Params.L, hW.lam_eq]
  obtain ⟨-, hNII⟩ := eventually_side_conditions_of_rvm Z hR P hP
  obtain ⟨θ₀, hTail, hB0, hBto⟩ := family_tail_package Z P hP hlam hW
  obtain ⟨htrace, hfrob⟩ := hM
  have hLtop := tendsto_L_atTop P hP.lam_pos
  have h0 : ∀ᶠ T in atTop, 4 * rtrace ((Pf T).hat T (Z.Gz (Pf T) T))
      - frobSq ((Pf T).hat T (Z.Gz (Pf T) T))
      - 2 * (Z.N T (2 * T) : ℝ) - 3 * (NII Z T : ℝ)
      - θ₀ T / ((Pf T).a T * (Pf T).L T)
          * (4 + 2 * Real.sqrt (frobSq ((Pf T).hat T (Z.Gz (Pf T) T)))
            + θ₀ T / ((Pf T).a T * (Pf T).L T))
      ≤ (Z.N0s T (2 * T) : ℝ) := by
    filter_upwards [hTail, hW.poisson, hW.a_half, eventually_ge_atTop (0:ℝ),
      hLtop.eventually_gt_atTop 0] with T hTl hPo ha2 hT0 hLT
    have hLpos : 0 < (Pf T).L T := by rw [hL]; exact hLT
    exact seamA_mult2 hT0 ZeroSide.phiHatConj ZeroSide.phiHatReal hPo hTl (by linarith) hLpos
  have hNII_o : (fun T => (NII Z T : ℝ)) =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) := by
    obtain ⟨CII, hII⟩ := hNII
    have hO : (fun T => (NII Z T : ℝ)) =O[atTop] (fun T => Real.sqrt T * l T) := by
      refine IsBigO.of_bound CII ?_
      filter_upwards [hII, eventually_l_pos] with T h hl
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (by positivity)]
      simpa [mul_assoc] using h
    exact hO.trans_isLittleO (isLittleO_N_of_isLittleO_Tl Z hR isLittleO_sqrt_mul_l_Tl)
  exact count_certificate_fn κ (N := fun T => (Z.N T (2 * T) : ℝ)) (NII := fun T => (NII Z T : ℝ))
    (tr := fun T => rtrace ((Pf T).hat T (Z.Gz (Pf T) T)))
    (fr := fun T => frobSq ((Pf T).hat T (Z.Gz (Pf T) T)))
    (B := fun T => θ₀ T / ((Pf T).a T * (Pf T).L T)) (lower := fun T => (Z.N0s T (2 * T) : ℝ))
    (Eventually.of_forall fun T => frobSq_nonneg _) h0 hB0 hBto hNII_o (tendsto_N_atTop Z hR)
    htrace hfrob

include hR hP hlam hW in
/-- **(3/2 − κ/2 − ε)·N(T,2T) ≤ N_d(T,2T)** at fixed λ for a window FAMILY, abstract Z, from GzMoments. -/
theorem dist_bound_of_gzMoments_family {κ : ℝ} (hM : GzMoments Z Pf κ) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 2 - κ / 2 - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.Nd T (2 * T) := by
  have hL : ∀ T, (Pf T).L T = P.L T := fun T => by simp only [Params.L, hW.lam_eq]
  obtain ⟨-, hNII⟩ := eventually_side_conditions_of_rvm Z hR P hP
  obtain ⟨θ₀, hTail, hB0, hBto⟩ := family_tail_package Z P hP hlam hW
  obtain ⟨htrace, hfrob⟩ := hM
  have hLtop := tendsto_L_atTop P hP.lam_pos
  have h0 : ∀ᶠ T in atTop, 6 * rtrace ((Pf T).hat T (Z.Gz (Pf T) T))
      - frobSq ((Pf T).hat T (Z.Gz (Pf T) T))
      - 3 * (Z.N T (2 * T) : ℝ) - 5 * (NII Z T : ℝ)
      - θ₀ T / ((Pf T).a T * (Pf T).L T)
          * (6 + 2 * Real.sqrt (frobSq ((Pf T).hat T (Z.Gz (Pf T) T)))
            + θ₀ T / ((Pf T).a T * (Pf T).L T))
      ≤ 2 * (Z.Nd T (2 * T) : ℝ) := by
    filter_upwards [hTail, hW.poisson, hW.a_half, eventually_ge_atTop (0:ℝ),
      hLtop.eventually_gt_atTop 0] with T hTl hPo ha2 hT0 hLT
    have hLpos : 0 < (Pf T).L T := by rw [hL]; exact hLT
    exact seamA_mult3 hT0 ZeroSide.phiHatConj ZeroSide.phiHatReal hPo hTl (by linarith) hLpos
  have hNII_o : (fun T => (NII Z T : ℝ)) =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) := by
    obtain ⟨CII, hII⟩ := hNII
    have hO : (fun T => (NII Z T : ℝ)) =O[atTop] (fun T => Real.sqrt T * l T) := by
      refine IsBigO.of_bound CII ?_
      filter_upwards [hII, eventually_l_pos] with T h hl
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (by positivity)]
      simpa [mul_assoc] using h
    exact hO.trans_isLittleO (isLittleO_N_of_isLittleO_Tl Z hR isLittleO_sqrt_mul_l_Tl)
  exact count_certificate_c3_fn κ (N := fun T => (Z.N T (2 * T) : ℝ)) (NII := fun T => (NII Z T : ℝ))
    (tr := fun T => rtrace ((Pf T).hat T (Z.Gz (Pf T) T)))
    (fr := fun T => frobSq ((Pf T).hat T (Z.Gz (Pf T) T)))
    (B := fun T => θ₀ T / ((Pf T).a T * (Pf T).L T)) (lower := fun T => (Z.Nd T (2 * T) : ℝ))
    (Eventually.of_forall fun T => frobSq_nonneg _) h0 hB0 hBto hNII_o (tendsto_N_atTop Z hR)
    htrace hfrob

end Family

/-! ## §A2′. Instantiation at the zeros of ξ′: FixedLamBounds from the four component Props (flat window) -/

/-- **[XF′ Thm 8.2] at fixed λ, flat window, from the interface Props.**  Every undischarged classical
input is an explicit binder: (F2) hF2, the seam hs, H-RvM for ξ′ hR; the analytic content arrives as the
three interface propositions instantiated at Z := xiDerivZeros hF2 hs and the flat family fun _ => P. -/
theorem fixedLam_flat (hF2 : XiDerivZerosInStrip) (hs : XiDerivSeam) (hR : XiDerivRvM hF2 hs)
    {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ) {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1)
    (hCM : CoeffMoments (xiDerivZeros hF2 hs) (fun _ => paramsOf ϱ lam) xiCoeffFamily
      (kappaXi lam vFlat))
    (hTT : XiTraceTransfer (xiDerivZeros hF2 hs) (fun _ => paramsOf ϱ lam) xiCoeffFamily) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 - kappaXi lam vFlat - ε) * (Ncount T (2 * T) : ℝ) ≤ (N0simple T (2 * T) : ℝ) ∧
      (3 / 2 - kappaXi lam vFlat / 2 - ε) * (Ncount T (2 * T) : ℝ) ≤ (Ndist T (2 * T) : ℝ) := by
  have hP := paramsOf_valid hϱ h0 h1.le
  have hκ := kappa_nonneg_of_coeffMoments _ hR _ _ hCM
  have hM := gzMoments_of_transfer _ _ _ hκ hCM hTT
  have hlam' : (paramsOf ϱ lam).lam < 1 := h1
  have hA := simple_bound_of_gzMoments (xiDerivZeros hF2 hs) hR (paramsOf ϱ lam) hP hlam' hM
  have hB := dist_bound_of_gzMoments (xiDerivZeros hF2 hs) hR (paramsOf ϱ lam) hP hlam' hM
  intro ε hε
  obtain ⟨T₁, hT₁⟩ := hA ε hε
  obtain ⟨T₂, hT₂⟩ := hB ε hε
  refine ⟨max T₁ T₂, fun T hT => ⟨?_, ?_⟩⟩
  · simpa using hT₁ T (le_trans (le_max_left _ _) hT)
  · simpa using hT₂ T (le_trans (le_max_right _ _) hT)

/-- **[XF′ Thm 8.2] at fixed λ for a window family Pf (e.g. (paramsOf ϱ lam).atV vQuartic) and profile v,
from the interface Props + the family's zero-side facts (`WindowZeroSide`).** -/
theorem fixedLam_family (hF2 : XiDerivZerosInStrip) (hs : XiDerivSeam) (hR : XiDerivRvM hF2 hs)
    {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ) {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1)
    {v : ℝ → ℝ} {Pf : ℝ → Params} (hW : WindowZeroSide (xiDerivZeros hF2 hs) (paramsOf ϱ lam) Pf)
    (hCM : CoeffMoments (xiDerivZeros hF2 hs) Pf xiCoeffFamily (kappaXi lam v))
    (hTT : XiTraceTransfer (xiDerivZeros hF2 hs) Pf xiCoeffFamily) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 - kappaXi lam v - ε) * (Ncount T (2 * T) : ℝ) ≤ (N0simple T (2 * T) : ℝ) ∧
      (3 / 2 - kappaXi lam v / 2 - ε) * (Ncount T (2 * T) : ℝ) ≤ (Ndist T (2 * T) : ℝ) := by
  have hP := paramsOf_valid hϱ h0 h1.le
  have hκ := kappa_nonneg_of_coeffMoments _ hR _ _ hCM
  have hM := gzMoments_of_transfer _ _ _ hκ hCM hTT
  have hlam' : (paramsOf ϱ lam).lam < 1 := h1
  have hA := simple_bound_of_gzMoments_family (xiDerivZeros hF2 hs) hR (paramsOf ϱ lam) hP hlam' hW hM
  have hB := dist_bound_of_gzMoments_family (xiDerivZeros hF2 hs) hR (paramsOf ϱ lam) hP hlam' hW hM
  intro ε hε
  obtain ⟨T₁, hT₁⟩ := hA ε hε
  obtain ⟨T₂, hT₂⟩ := hB ε hε
  refine ⟨max T₁ T₂, fun T hT => ⟨?_, ?_⟩⟩
  · simpa using hT₁ T (le_trans (le_max_left _ _) hT)
  · simpa using hT₂ T (le_trans (le_max_right _ _) hT)

/-- ε-free decimals from a strict certified inequality at one λ (used by Final.lean with CertFlat /
CertQuartic): if c < 2 − κ and cd < 3/2 − κ/2 strictly and the fixed-λ bounds hold for κ, then
c·N ≤ N₀ˢ and cd·N ≤ N_d eventually. -/
theorem headline_of_strict {κ c cd : ℝ} {N lowS lowD : ℝ → ℝ} (hN : ∀ T, 0 ≤ N T)
    (hc : c < 2 - κ) (hcd : cd < 3 / 2 - κ / 2)
    (h : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 - κ - ε) * N T ≤ lowS T ∧ (3 / 2 - κ / 2 - ε) * N T ≤ lowD T) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, c * N T ≤ lowS T ∧ cd * N T ≤ lowD T := by
  set ε := min (2 - κ - c) (3 / 2 - κ / 2 - cd) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
  obtain ⟨T₀, hT₀⟩ := h ε hε0
  refine ⟨T₀, fun T hT => ?_⟩
  obtain ⟨h1, h2⟩ := hT₀ T hT
  have hNT := hN T
  have e1 : c ≤ 2 - κ - ε := by have := min_le_left (2 - κ - c) (3 / 2 - κ / 2 - cd); linarith
  have e2 : cd ≤ 3 / 2 - κ / 2 - ε := by have := min_le_right (2 - κ - c) (3 / 2 - κ / 2 - cd); linarith
  exact ⟨(mul_le_mul_of_nonneg_right e1 hNT).trans h1, (mul_le_mul_of_nonneg_right e2 hNT).trans h2⟩

/-! ## §A2″. Interval additivity and the cumulative (0,T] form for the ξ′ configuration
(pattern: Zeta23/Main.lean cumulative_of_dyadic; Zeta23.Assembly.dyadic is generic). -/

section Cumulative
variable (hF2 : XiDerivZerosInStrip) (hs : XiDerivSeam)

include hF2 hs in
lemma Ncount_add {a b d : ℝ} (hab : a ≤ b) (hbd : b ≤ d) :
    Ncount a d = Ncount a b + Ncount b d := by
  simpa using Assembly.N_add (xiDerivZeros hF2 hs) hab hbd

include hF2 hs in
lemma N0simple_add {a b d : ℝ} (hab : a ≤ b) (hbd : b ≤ d) :
    N0simple a d = N0simple a b + N0simple b d := by
  simpa using Assembly.N0s_add (xiDerivZeros hF2 hs) hab hbd

include hF2 hs in
lemma Ndist_add {a b d : ℝ} (hab : a ≤ b) (hbd : b ≤ d) :
    Ndist a d = Ndist a b + Ndist b d := by
  simpa using Assembly.Nd_add (xiDerivZeros hF2 hs) hab hbd

/-- H-RvM for ξ′ ⇒ N_{ξ′}(0,T) → ∞. -/
lemma tendsto_Ncount_zero_atTop (hR : XiDerivRvM hF2 hs) :
    Tendsto (fun T => (Ncount 0 T : ℝ)) atTop atTop := by
  have h1 : Tendsto (fun T : ℝ => ((xiDerivZeros hF2 hs).N (T / 2) (2 * (T / 2)) : ℝ)) atTop atTop :=
    (tendsto_N_atTop (xiDerivZeros hF2 hs) hR).comp (tendsto_id.atTop_div_const two_pos)
  refine tendsto_atTop_mono' _ ?_ h1
  filter_upwards [eventually_ge_atTop 0] with T hT
  have hsplit := Assembly.N_add (xiDerivZeros hF2 hs) (a := 0) (b := T / 2) (c := T) (by linarith)
    (by linarith)
  have : 2 * (T / 2) = T := by ring
  rw [this]
  simp only [xiDerivZeros_N] at hsplit ⊢
  exact_mod_cast hsplit ▸ Nat.le_add_left _ _

/-- dyadic summation for one interval-additive count f against N_{ξ′}. -/
theorem cumulative_of_dyadic (hR : XiDerivRvM hF2 hs) {c : ℝ} {f : ℝ → ℝ → ℕ}
    (hf_add : ∀ a b d : ℝ, a ≤ b → b ≤ d → f a d = f a b + f b d)
    (h : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (c - ε) * (Ncount T (2 * T) : ℝ) ≤ f T (2 * T)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (c - ε) * (Ncount 0 T : ℝ) ≤ f 0 T := by
  refine Assembly.dyadic (f := fun a b => (f a b : ℝ)) (g := fun a b => (Ncount a b : ℝ))
    (c := c) ?_ ?_ (fun _ _ => Nat.cast_nonneg _) (fun _ _ => Nat.cast_nonneg _)
    (tendsto_Ncount_zero_atTop hF2 hs hR) h
  · intro a b d hab hbd
    exact_mod_cast hf_add a b d hab hbd
  · intro a b d hab hbd
    exact_mod_cast Ncount_add hF2 hs hab hbd

/-- the fixed-λ pair of ε-bounds on dyadic windows ⇒ the same pair on (0,T]. -/
theorem cumulative_of_fixedLam (hR : XiDerivRvM hF2 hs) {κ : ℝ}
    (h : ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 - κ - ε) * (Ncount T (2 * T) : ℝ) ≤ (N0simple T (2 * T) : ℝ) ∧
      (3 / 2 - κ / 2 - ε) * (Ncount T (2 * T) : ℝ) ≤ (Ndist T (2 * T) : ℝ)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 - κ - ε) * (Ncount 0 T : ℝ) ≤ (N0simple 0 T : ℝ) ∧
      (3 / 2 - κ / 2 - ε) * (Ncount 0 T : ℝ) ≤ (Ndist 0 T : ℝ) := by
  have hA := cumulative_of_dyadic hF2 hs hR (c := 2 - κ) (f := N0simple)
    (fun a b d => N0simple_add hF2 hs) fun ε hε => by
      obtain ⟨T₀, hT₀⟩ := h ε hε
      exact ⟨T₀, fun T hT => (hT₀ T hT).1⟩
  have hB := cumulative_of_dyadic hF2 hs hR (c := 3 / 2 - κ / 2) (f := Ndist)
    (fun a b d => Ndist_add hF2 hs) fun ε hε => by
      obtain ⟨T₀, hT₀⟩ := h ε hε
      exact ⟨T₀, fun T hT => (hT₀ T hT).2⟩
  intro ε hε
  obtain ⟨T₁, hT₁⟩ := hA ε hε
  obtain ⟨T₂, hT₂⟩ := hB ε hε
  exact ⟨max T₁ T₂, fun T hT =>
    ⟨hT₁ T ((le_max_left _ _).trans hT), hT₂ T ((le_max_right _ _).trans hT)⟩⟩

end Cumulative

/-! ## §A4. The Z′ layer: the same assembly at Z := wZeros hZ hs (zeros of W = ζ′ + L₂ζ with |Im| ≥ t₀)
[XF′ §9].  Everything in §A1–§A3 is generic in Z; only the count seam differs (wZeros_N/_N0s/_Nd need
t₀ ≤ T, Statement §6), so the W headline holds for T ≥ max T₀ t₀.  Constants: wCoeffFamily has the same
density D₁, hence the same κ₁(λ, v) and the same certificates CertFlat / CertQuartic. -/

/-- **[XF′ Thm 9.4] at fixed λ, window family Pf, from the interface Props instantiated at wZeros.** -/
theorem fixedLam_family_W {t₀ : ℝ} (hZ : WZerosInStrip t₀) (hs : WSeam t₀)
    (hR : RiemannVonMangoldt (wZeros hZ hs))
    {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ) {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1)
    {v : ℝ → ℝ} {Pf : ℝ → Params} (hW : WindowZeroSide (wZeros hZ hs) (paramsOf ϱ lam) Pf)
    (hCM : CoeffMoments (wZeros hZ hs) Pf wCoeffFamily (kappaXi lam v))
    (hTT : XiTraceTransfer (wZeros hZ hs) Pf wCoeffFamily) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 - kappaXi lam v - ε) * (NcountW T (2 * T) : ℝ) ≤ (N0simpleW T (2 * T) : ℝ) ∧
      (3 / 2 - kappaXi lam v / 2 - ε) * (NcountW T (2 * T) : ℝ) ≤ (NdistW T (2 * T) : ℝ) := by
  have hP := paramsOf_valid hϱ h0 h1.le
  have hκ := kappa_nonneg_of_coeffMoments _ hR _ _ hCM
  have hM := gzMoments_of_transfer _ _ _ hκ hCM hTT
  have hlam' : (paramsOf ϱ lam).lam < 1 := h1
  have hA := simple_bound_of_gzMoments_family (wZeros hZ hs) hR (paramsOf ϱ lam) hP hlam' hW hM
  have hB := dist_bound_of_gzMoments_family (wZeros hZ hs) hR (paramsOf ϱ lam) hP hlam' hW hM
  intro ε hε
  obtain ⟨T₁, hT₁⟩ := hA ε hε
  obtain ⟨T₂, hT₂⟩ := hB ε hε
  refine ⟨max (max T₁ T₂) t₀, fun T hT => ?_⟩
  have ht : t₀ ≤ T := (le_max_right _ _).trans hT
  have h12 : max T₁ T₂ ≤ T := (le_max_left _ _).trans hT
  have hA' := hT₁ T ((le_max_left _ _).trans h12)
  have hB' := hT₂ T ((le_max_right _ _).trans h12)
  rw [wZeros_N hZ hs ht, wZeros_N0s hZ hs ht] at hA'
  rw [wZeros_N hZ hs ht, wZeros_Nd hZ hs ht] at hB'
  exact ⟨hA', hB'⟩

end XiPrime
end Zeta23

end
