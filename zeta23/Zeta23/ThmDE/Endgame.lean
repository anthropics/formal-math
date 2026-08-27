/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmDE/Endgame.lean — the §6 endgame for L(s,χ) with the
Montgomery–Taylor ratio constant: paper [thm:E], last clause ("Theorem D holds likewise.").

A mirror of Zeta23/ThmD/Endgame.lean (thmD_abstract / thmD_BC_core / thmD_simple_abstract /
thmD_dist_abstract) with the χ-substitutions of Zeta23/ThmE/AssemblyQ.lean:
  * (H : PaperInputs Z) ↦ (hRvM : ThmE.RiemannVonMangoldtChi q Z) — the only use of H there was
    H.RvM (growth of N(T,2T)): tendsto_N_atTop ↦ ThmE.tendsto_N_atTop_chi,
    isLittleO_N_of_isLittleO_Tl ↦ ThmE.isLittleO_N_of_isLittleO_Tl_chi,
    eventually_N_ge ↦ ThmE.eventually_N_ge_chi;
  * TracesBoundsD ↦ ThmDE.TracesBoundsDChi P q (cRatio taken at λ_{1,χ} = ThmE.lam1q P q T);
  * the prime-side matrix/traces (P.atD T).Gp / trGtilde / trGtildeSq ↦ ThmE.GpChi /
    trGtildeChi / trGtildeSqChi of (P.atD T) (rtrace_tilde_GpChi, frobSq_tilde_GpChi,
    GpChi_isHermitian).
Everything else (seamA, seamA_BC, N0star_lower_c, nplus_lower, nplus_ge_explicit, err_isLittleO,
eps_form_of_isLittleO, the o-calculus) is q-independent and reused verbatim.  Conclusions carry
the constants 2 − 1/c∞, 2c∞ − 1, c∞ for an abstract limit c∞ of cRatio(λ_{1,χ}(T); a_T, b_T, J_T).
-/
import Zeta23.ThmE.AssemblyQ
import Zeta23.ThmDE.TracesHyp
import Zeta23.ThmD.ParamsD

noncomputable section

open Filter Asymptotics Topology Real
open RHLinalg

namespace Zeta23
namespace ThmDE

open Assembly ThmD ThmE

section Star

/-- **Theorem D for L(s,χ), Thm-A line, at fixed λ ∈ (0,1), abstract zero configuration and abstract
D-traces.**  If the D-trace package holds for data (a_T, b_T, J_T, trG̃, trG̃²) against N(T,2T),
the ratio constant cRatio(λ₁(T); a_T, b_T, J_T) tends to c∞ > 0, a_T ∈ [1/2, 1] eventually, and
the zero-side inputs hold for the window-realizing family P.atD T whose prime-side traces and
taper constant ARE (trG̃, trG̃², a_T), then for every ε > 0, eventually
N₀*(T,2T) ≥ (2 − 1/c∞ − ε) N(T,2T). -/
theorem thmDChi_abstract (Z : ZeroConfig) (κ : ℕ) {q : ℕ} (hq : 1 ≤ q) (cf : ℕ → ℂ)
    (P : Params) (hP : P.Valid) (hlam : P.lam < 1)
    (hRvM : RiemannVonMangoldtChi q Z)
    (aT bT JT trG trG2 : ℝ → ℝ)
    (hTr : TracesBoundsDChi P q aT bT JT trG trG2 (fun T => (Z.N T (2 * T) : ℝ)))
    {c : ℝ} (hc0 : 0 < c)
    (hc : Tendsto (fun T => cRatio (lam1q P q T) (aT T) (bT T) (JT T)) atTop (𝓝 c))
    (ha : ∀ᶠ T in atTop, 1 / 2 ≤ aT T ∧ aT T ≤ 1)
    (hBlock : ∀ᶠ T in atTop, BlockInputs Z (P.atD T) T)
    (θ₀ : ℝ → ℝ) (hTail : ∀ᶠ T in atTop, TailInputs Z (P.atD T) T (θ₀ T))
    (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop, (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop, Z.Gz (P.atD T) T = GpChi (P.atD T) κ q cf T)
    (hId : ∀ᶠ T in atTop, trGtildeChi (P.atD T) κ q cf T = trG T ∧
      trGtildeSqChi (P.atD T) κ q cf T = trG2 T ∧ (P.atD T).a T = aT T)
    (hcalE : Tendsto P.calE atTop (𝓝 0)) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 - c⁻¹ - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.N0star T (2 * T) := by
  have hlam0 := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hlam.le
  obtain ⟨C₁, hC₁, T₁, htr1⟩ := hTr.tr1
  obtain ⟨C₂, hC₂, T₂, hfr2⟩ := hTr.frhat
  obtain ⟨Cθ, hθ⟩ := hθ₀
  obtain ⟨CII, hII⟩ := hNII
  -- the functions of T (abbreviations)
  set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hNdef
  set cinv : ℝ → ℝ := fun T => (cRatio (lam1q P q T) (aT T) (bT T) (JT T))⁻¹ with hcinv
  set R₁ : ℝ → ℝ := fun T => C₁ * Real.sqrt (P.X T) / aT T with hR₁
  set R₂ : ℝ → ℝ := fun T => C₂ * P.calE T * (cinv T * N T) with hR₂
  set B : ℝ → ℝ := fun T => θ₀ T / (aT T * P.L T) with hBdef
  set err : ℝ → ℝ := fun T => (4 * R₁ T + R₂ T + 3 * (NII Z T : ℝ)
      + B T * (4 + 2 * Real.sqrt (cinv T * N T + R₂ T) + B T)) + |cinv T - c⁻¹| * N T with herr
  -- basic limits
  have hLtop := tendsto_L_atTop P hlam0
  have hcinv_to : Tendsto cinv atTop (𝓝 c⁻¹) := hc.inv₀ hc0.ne'
  ------------------------------------------------------------------
  -- (1) the main inequality, eventually in T
  ------------------------------------------------------------------
  have hmain : ∀ᶠ T in atTop, (2 - c⁻¹) * N T - err T ≤ (Z.N0star T (2 * T) : ℝ) := by
    filter_upwards [hBlock, hTail, hGzGp, hId, ha, eventually_ge_atTop T₁,
      eventually_ge_atTop T₂, eventually_ge_atTop (0:ℝ), eventually_l_pos,
      eventually_calE_nonneg P hlam0 (zero_le_one.trans hP.one_le_w)]
      with T hBl hTl hGG hid ha2 hT₁ hT₂ hT0 hl hE0
    obtain ⟨hidtr, hidfr, hida⟩ := hid
    have hapos' : 0 < aT T := by linarith [ha2.1]
    have haposD : 0 < (P.atD T).a T := by rw [hida]; exact hapos'
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
    -- Seam A for the window-realizing parameters
    have hA := seamA hT0 hBl hTl haposD hLpos
    -- the hat-unit traces in terms of the abstract data
    have hrt : rtrace ((P.atD T).hat T (Z.Gz (P.atD T) T)) = (aT T * P.L T)⁻¹ * trG T := by
      rw [rtrace_hat, hGG, rtrace_tilde_GpChi, hidtr, hida]; rfl
    have hfr : frobSq ((P.atD T).hat T (Z.Gz (P.atD T) T))
        = ((aT T * P.L T)⁻¹) ^ 2 * trG2 T := by
      rw [frobSq_hat, hGG, frobSq_tilde_GpChi, hidfr, hida]; rfl
    have haL : (P.atD T).a T * (P.atD T).L T = aT T * P.L T := by rw [hida]; rfl
    rw [hrt, hfr, haL] at hA
    -- |tr Ĝ − N| ≤ R₁
    have htr : |(aT T * P.L T)⁻¹ * trG T - N T| ≤ R₁ T :=
      trGhat_sub_N_le hapos' hLpos (by simpa only using htr1 T hT₁)
    -- ‖Ĝ‖² ≤ cinv N + R₂
    have hfrb : ((aT T * P.L T)⁻¹) ^ 2 * trG2 T ≤ cinv T * N T + R₂ T := by
      have h := hfr2 T hT₂
      simp only at h
      have h1 : trG2 T / (aT T * P.L T) ^ 2 - cinv T * N T ≤ C₂ * P.calE T * (cinv T * N T) := by
        rw [← mul_assoc] at h
        exact le_trans (le_trans (le_max_left _ 0) (le_abs_self _)) h
      have e : ((aT T * P.L T)⁻¹) ^ 2 * trG2 T = trG2 T / (aT T * P.L T) ^ 2 := by
        rw [inv_pow, div_eq_inv_mul]
      rw [e]; simp only [hR₂]; linarith
    have hB₀ : 0 ≤ B T := div_nonneg hTl.theta_nonneg (mul_pos hapos' hLpos).le
    have h := N0star_lower_c hB₀ hA htr hfrb
    have hN0 : 0 ≤ N T := Nat.cast_nonneg _
    have hcd : (2 - c⁻¹) * N T - |cinv T - c⁻¹| * N T ≤ (2 - cinv T) * N T := by
      have h1 := mul_le_mul_of_nonneg_right (le_abs_self (cinv T - c⁻¹)) hN0
      linarith [h1]
    simp only [herr, hR₁, hR₂, hBdef, hNdef] at h hcd ⊢
    linarith
  ------------------------------------------------------------------
  -- (2) err = o(N)
  ------------------------------------------------------------------
  have hNtop : Tendsto N atTop atTop := tendsto_N_atTop_chi q Z hq hRvM
  -- R₁ = o(N)
  have o1 : R₁ =o[atTop] N := by
    have hbd : (fun T => C₁ / aT T) =O[atTop] (fun _ => (1:ℝ)) := by
      refine isBigO_one_of_abs_le (C := 2 * C₁) ?_
      filter_upwards [ha] with T ha2
      rw [abs_of_nonneg (div_nonneg hC₁.le (by linarith [ha2.1]))]
      rw [div_le_iff₀ (by linarith [ha2.1])]; nlinarith [ha2.1]
    have := isLittleO_of_bdd_mul hbd
      (isLittleO_N_of_isLittleO_Tl_chi q Z hq hRvM (isLittleO_sqrtX_Tl P hlam0 hlam1))
    exact this.congr_left fun T => by simp only [hR₁]; ring
  -- cinv is eventually in [0, 2/c] and bounded
  have hcinv_bd : ∀ᶠ T in atTop, 0 ≤ cinv T ∧ cinv T ≤ 2 * c⁻¹ := by
    have hcpos : (0:ℝ) < c⁻¹ := inv_pos.mpr hc0
    filter_upwards [hcinv_to.eventually (eventually_ge_nhds hcpos),
      hcinv_to.eventually (eventually_le_nhds (show c⁻¹ < 2 * c⁻¹ by linarith))] with T h1 h2
    exact ⟨h1, h2⟩
  have hcinvO : cinv =O[atTop] (fun _ => (1:ℝ)) := by
    refine isBigO_one_of_abs_le (C := 2 * c⁻¹) ?_
    filter_upwards [hcinv_bd] with T h
    rw [abs_of_nonneg h.1]; exact h.2
  -- R₂ = o(N)
  have o2 : R₂ =o[atTop] N := by
    have hcE0 : Tendsto (fun T => C₂ * P.calE T) atTop (𝓝 0) := by
      simpa using hcalE.const_mul C₂
    have i1 : (fun T => cinv T * N T) =O[atTop] N := by
      have := hcinvO.mul (isBigO_refl N atTop)
      simpa using this
    have := ((isLittleO_one_iff ℝ).2 hcE0).mul_isBigO i1
    refine (this.congr_left fun T => ?_).congr_right fun T => by simp
    simp only [hR₂]
  -- N(I′∖I) = o(N)
  have o3 : (fun T => (NII Z T : ℝ)) =o[atTop] N := by
    have hO : (fun T => (NII Z T : ℝ)) =O[atTop] (fun T => Real.sqrt T * l T) := by
      refine IsBigO.of_bound CII ?_
      filter_upwards [hII, eventually_l_pos] with T h hl
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (by positivity)]
      simpa [mul_assoc] using h
    exact hO.trans_isLittleO (isLittleO_N_of_isLittleO_Tl_chi q Z hq hRvM isLittleO_sqrt_mul_l_Tl)
  -- B → 0
  have o4 : Tendsto B atTop (𝓝 0) := by
    have hup : Tendsto (fun T => 2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) atTop (𝓝 0) := by
      simpa using (tendsto_theta_over_L P hlam0 hlam1).const_mul (2 * |Cθ|)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hTail, ha, eventually_l_pos] with T hTl ha2 hl
      have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
      exact div_nonneg hTl.theta_nonneg (by nlinarith [ha2.1])
    · filter_upwards [hTail, ha, eventually_l_pos, hθ, eventually_gt_atTop (0:ℝ)]
        with T hTl ha2 hl hθT hT0
      have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
      have hapos' : 0 < aT T := by linarith [ha2.1]
      have hq : 0 ≤ l T * T ^ (P.lam / 2 - 1) / P.L T := by positivity
      simp only [hBdef]
      rw [div_le_iff₀ (mul_pos hapos' hLpos)]
      calc θ₀ T ≤ Cθ * l T * T ^ (P.lam / 2 - 1) := hθT
        _ ≤ |Cθ| * l T * T ^ (P.lam / 2 - 1) := by gcongr; exact le_abs_self _
        _ = |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T := by field_simp
        _ ≤ (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (aT T * P.L T) := by
          have : |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T
              = (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (1 / 2 * P.L T) := by ring
          rw [this]; gcongr; exact ha2.1
  -- the bracket and the constant-drift term
  have o5 := err_isLittleO (R₁ := R₁) (R₂ := R₂) (NII := fun T => (NII Z T : ℝ)) (B := B)
    (cl := cinv) hNtop o1 o2 o3 o4 hcinv_bd
  have o6 : (fun T => |cinv T - c⁻¹| * N T) =o[atTop] N := by
    refine isLittleO_of_tendsto_zero_mul ?_
    have : Tendsto (fun T => cinv T - c⁻¹) atTop (𝓝 0) := by
      simpa using hcinv_to.sub_const c⁻¹
    simpa using this.abs
  have herr_o : err =o[atTop] N := o5.add o6
  ------------------------------------------------------------------
  -- (3) conclude
  ------------------------------------------------------------------
  exact eps_form_of_isLittleO hmain (Eventually.of_forall fun T => Nat.cast_nonneg _) herr_o

end Star

section BC

/-- **Theorem D for L(s,χ), Thm-B/C lines, at fixed λ ∈ (0,1) — common core** (mirror of
'Assembly.thmBC_core' with F(λ₁) ↦ cRatio(λ₁; a_T, b_T, J_T) → c∞): there is R = o(N) with,
eventually in T, (2c∞ − 1)N − 2R ≤ N₀ˢ(T,2T) and c∞·N − R ≤ N_d(T,2T). -/
theorem thmDChi_BC_core (Z : ZeroConfig) (κ : ℕ) {q : ℕ} (hq : 1 ≤ q) (cf : ℕ → ℂ)
    (P : Params) (hP : P.Valid) (hlam : P.lam < 1)
    (hRvM : RiemannVonMangoldtChi q Z)
    (aT bT JT trG trG2 : ℝ → ℝ)
    (hTr : TracesBoundsDChi P q aT bT JT trG trG2 (fun T => (Z.N T (2 * T) : ℝ)))
    {c : ℝ} (hc0 : 0 < c)
    (hc : Tendsto (fun T => cRatio (lam1q P q T) (aT T) (bT T) (JT T)) atTop (𝓝 c))
    (ha : ∀ᶠ T in atTop, 1 / 2 ≤ aT T ∧ aT T ≤ 1)
    (hBlock : ∀ᶠ T in atTop, BlockInputs Z (P.atD T) T)
    (θ₀ : ℝ → ℝ) (hTail : ∀ᶠ T in atTop, TailInputs Z (P.atD T) T (θ₀ T))
    (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop, (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop, Z.Gz (P.atD T) T = GpChi (P.atD T) κ q cf T)
    (hId : ∀ᶠ T in atTop, trGtildeChi (P.atD T) κ q cf T = trG T ∧
      trGtildeSqChi (P.atD T) κ q cf T = trG2 T ∧ (P.atD T).a T = aT T) :
    ∃ R : ℝ → ℝ, R =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) ∧
      ∀ᶠ T in atTop,
        (2 * c - 1) * (Z.N T (2 * T) : ℝ) - 2 * R T ≤ Z.N0s T (2 * T) ∧
        c * (Z.N T (2 * T) : ℝ) - R T ≤ Z.Nd T (2 * T) := by
  have hlam0 := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hlam.le
  have hcalE := calE_tendsto_zero P hlam0 hlam1 (zero_le_one.trans hP.one_le_w)
  obtain ⟨C₃, hC₃, T₃, hratio⟩ := hTr.ratio
  obtain ⟨C₄, hC₄, T₄, htr1⟩ := hTr.tr1
  obtain ⟨Cθ, hθ⟩ := hθ₀
  obtain ⟨CII, hII⟩ := hNII
  set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hNdef
  set cT : ℝ → ℝ := fun T => cRatio (lam1q P q T) (aT T) (bT T) (JT T) with hcT
  set x : ℝ → ℝ := fun T => θ₀ T * (P.d T : ℝ) / trG T with hxdef
  set R : ℝ → ℝ := fun T => (C₃ * P.calE T * (cT T * N T)
      + 2 * x T * ((1 + C₃ * P.calE T) * (cT T * N T)))
      + (NII Z T : ℝ) + |cT T - c| * N T with hRdef
  have hNtop : Tendsto N atTop atTop := tendsto_N_atTop_chi q Z hq hRvM
  have hcE0 : Tendsto (fun T => C₃ * P.calE T) atTop (𝓝 0) := by simpa using hcalE.const_mul C₃
  -- √X ≤ N/(4C₄) eventually (√X = o(Tl) = o(N))
  have hsqrtX : ∀ᶠ T in atTop, C₄ * Real.sqrt (P.X T) ≤ N T / 4 := by
    have ho := isLittleO_N_of_isLittleO_Tl_chi q Z hq hRvM (isLittleO_sqrtX_Tl P hlam0 hlam1)
    have h := ho.def (show (0:ℝ) < 1 / (4 * C₄) by positivity)
    filter_upwards [h] with T hT
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (Nat.cast_nonneg _)] at hT
    have : C₄ * Real.sqrt (P.X T) ≤ C₄ * (1 / (4 * C₄) * N T) :=
      mul_le_mul_of_nonneg_left hT hC₄.le
    calc C₄ * Real.sqrt (P.X T) ≤ C₄ * (1 / (4 * C₄) * N T) := this
      _ = N T / 4 := by field_simp
  -- Step 0: eventually tr G̃ ≥ L N / 4 > 0 and x ≤ 8(|Cθ|+1) T^{λ/2−1} (so θ₀ d < tr G̃ and x → 0).
  have hx : ∀ᶠ T in atTop, 0 < trG T ∧ 0 ≤ x T ∧
      x T ≤ 8 * (|Cθ| + 1) * T ^ (P.lam / 2 - 1) ∧ θ₀ T * (P.d T : ℝ) < trG T := by
    filter_upwards [hTail, hθ, ha, eventually_ge_atTop T₄, eventually_N_ge_chi q Z hq hRvM, eventually_l_pos,
      eventually_gt_atTop (0:ℝ), hsqrtX,
      (tendsto_rpow_halflam_sub_one P hlam1).eventually
        (eventually_lt_nhds (show (0:ℝ) < 1 / (16 * (|Cθ| + 1)) by positivity))]
      with T hTl hθT ha2 hT₄ hNge hl hT0 hsX hTs
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
    have h1 := (abs_le.mp (by simpa only using htr1 T hT₄)).1
    have hN0 : 0 ≤ N T := Nat.cast_nonneg _
    have hLN : 0 < P.L T * N T := by
      have : 0 < T * l T / (4 * Real.pi) := by positivity
      exact mul_pos hLpos (this.trans_le hNge)
    have htrG : P.L T * N T / 4 ≤ trG T := by
      -- trG ≥ a L N − C₄ L √X ≥ L N/2 − L N/4
      have e1 : aT T * P.L T * N T ≥ 1 / 2 * (P.L T * N T) := by nlinarith [ha2.1, hLN.le]
      have e2 : C₄ * (P.L T * Real.sqrt (P.X T)) ≤ P.L T * (N T / 4) := by
        have := mul_le_mul_of_nonneg_left hsX hLpos.le
        linarith [this]
      simp only [hNdef] at h1 e1 e2 ⊢
      nlinarith [h1, e1, e2]
    have htrGpos : 0 < trG T := lt_of_lt_of_le (by positivity) htrG
    have hd : (P.d T : ℝ) ≤ P.L T * T / (2 * Real.pi) := d_le P (by positivity)
    have hθ' : θ₀ T ≤ (|Cθ| + 1) * l T * T ^ (P.lam / 2 - 1) := by
      refine hθT.trans ?_
      have : Cθ ≤ |Cθ| + 1 := by linarith [le_abs_self Cθ]
      gcongr
    have hθ0 := hTl.theta_nonneg
    have hnum : θ₀ T * (P.d T : ℝ)
        ≤ ((|Cθ| + 1) * l T * T ^ (P.lam / 2 - 1)) * (P.L T * T / (2 * Real.pi)) :=
      mul_le_mul hθ' hd (Nat.cast_nonneg _) (hθ0.trans hθ')
    have hden : P.L T * (T * l T / (4 * Real.pi)) / 4 ≤ trG T :=
      le_trans (by gcongr) htrG
    have hxle : x T ≤ 8 * (|Cθ| + 1) * T ^ (P.lam / 2 - 1) := by
      simp only [hxdef]
      rw [div_le_iff₀ htrGpos]
      calc θ₀ T * (P.d T : ℝ)
          ≤ ((|Cθ| + 1) * l T * T ^ (P.lam / 2 - 1)) * (P.L T * T / (2 * Real.pi)) := hnum
        _ = 8 * (|Cθ| + 1) * T ^ (P.lam / 2 - 1) * (P.L T * (T * l T / (4 * Real.pi)) / 4) := by
          ring
        _ ≤ 8 * (|Cθ| + 1) * T ^ (P.lam / 2 - 1) * trG T := by gcongr
    refine ⟨htrGpos, div_nonneg (mul_nonneg hθ0 (Nat.cast_nonneg _)) htrGpos.le, hxle, ?_⟩
    have hx1 : x T < 1 := by
      refine hxle.trans_lt ?_
      have := (lt_div_iff₀ (show (0:ℝ) < 16 * (|Cθ| + 1) by positivity)).mp hTs
      nlinarith [abs_nonneg Cθ, Real.rpow_nonneg hT0.le (P.lam / 2 - 1)]
    simp only [hxdef] at hx1
    rwa [div_lt_one htrGpos] at hx1
  -- cT is eventually in [0, c+1]
  have hcT_bd : ∀ᶠ T in atTop, 0 ≤ cT T ∧ cT T ≤ c + 1 := by
    filter_upwards [hc.eventually (eventually_ge_nhds hc0),
      hc.eventually (eventually_le_nhds (show c < c + 1 by linarith))] with T h1 h2
    exact ⟨h1, h2⟩
  refine ⟨R, ?_, ?_⟩
  ------------------------------------------------------------------
  -- R = o(N)
  ------------------------------------------------------------------
  · have hFN : (fun T => cT T * N T) =O[atTop] N := by
      refine IsBigO.of_bound (c + 1) ?_
      filter_upwards [hcT_bd] with T hb
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg hb.1]
      exact mul_le_mul_of_nonneg_right hb.2 (abs_nonneg _)
    have o1 : (fun T => C₃ * P.calE T * (cT T * N T)) =o[atTop] N := by
      have := ((isLittleO_one_iff ℝ).2 hcE0).mul_isBigO hFN
      simpa using this
    have hxto : Tendsto x atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (by simpa using (tendsto_rpow_halflam_sub_one P hlam1).const_mul (8 * (|Cθ| + 1)))
        (hx.mono fun T h => h.2.1) (hx.mono fun T h => h.2.2.1)
    have o2 : (fun T => 2 * x T * ((1 + C₃ * P.calE T) * (cT T * N T))) =o[atTop] N := by
      have h2x : Tendsto (fun T => 2 * x T) atTop (𝓝 0) := by simpa using hxto.const_mul 2
      have hK : (fun T => 1 + C₃ * P.calE T) =O[atTop] (fun _ => (1:ℝ)) := by
        refine isBigO_one_of_abs_le (C := 2) ?_
        filter_upwards [hcE0.eventually (eventually_ge_nhds (show (-1:ℝ) < 0 by norm_num)),
          hcE0.eventually (eventually_le_nhds (show (0:ℝ) < 1 by norm_num))] with T h1 h2
        rw [abs_of_nonneg (by linarith)]; linarith
      have := ((isLittleO_one_iff ℝ).2 h2x).mul_isBigO (hK.mul hFN)
      simpa using this
    have o3 : (fun T => (NII Z T : ℝ)) =o[atTop] N := by
      have hO : (fun T => (NII Z T : ℝ)) =O[atTop] (fun T => Real.sqrt T * l T) := by
        refine IsBigO.of_bound CII ?_
        filter_upwards [hII, eventually_l_pos] with T h hl
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
          abs_of_nonneg (by positivity)]
        simpa [mul_assoc] using h
      exact hO.trans_isLittleO (isLittleO_N_of_isLittleO_Tl_chi q Z hq hRvM isLittleO_sqrt_mul_l_Tl)
    have o4 : (fun T => |cT T - c| * N T) =o[atTop] N := by
      refine isLittleO_of_tendsto_zero_mul ?_
      have : Tendsto (fun T => cT T - c) atTop (𝓝 0) := by
        simpa using hc.sub_const c
      simpa using this.abs
    exact ((o1.add o2).add o3).add o4
  ------------------------------------------------------------------
  -- the inequalities, eventually
  ------------------------------------------------------------------
  · filter_upwards [hBlock, hTail, hGzGp, hId, hx, eventually_ge_atTop T₃,
      eventually_ge_atTop (0:ℝ), eventually_l_pos,
      eventually_calE_nonneg P hlam0 (zero_le_one.trans hP.one_le_w)]
      with T hBl hTl hGG hid hxT hT₃ hT0 hl hE0
    obtain ⟨hidtr, hidfr, hida⟩ := hid
    have hGt : ((P.atD T).tilde T (Z.Gz (P.atD T) T)).IsHermitian := by
      rw [hGG]; exact isHermitian_tilde _ _ (GpChi_isHermitian _ _ _ _ _)
    -- [eq:zeroside2]
    have hZ := seamA_BC hT0 hBl hTl le_rfl hGt
    -- lem:CS, [eq:nplus-lower]
    have hθ0 := hTl.theta_nonneg
    have hrt : rtrace ((P.atD T).tilde T (Z.Gz (P.atD T) T)) = trG T := by
      rw [hGG, rtrace_tilde_GpChi, hidtr]
    have hfr : frobSq ((P.atD T).tilde T (Z.Gz (P.atD T) T)) = trG2 T := by
      rw [hGG, frobSq_tilde_GpChi, hidfr]
    have htr' : θ₀ T * (Fintype.card (Fin ((P.atD T).d T)) : ℝ)
        < rtrace ((P.atD T).tilde T (Z.Gz (P.atD T) T)) := by
      rw [card_fin_d, hrt]; exact hxT.2.2.2
    have hCS₀ := nplus_lower hGt hθ0 htr'
    rw [card_fin_d, hrt, hfr] at hCS₀
    have hCS : (trG T - θ₀ T * (P.d T : ℝ)) ^ 2 / trG2 T ≤ (posIndexAbove hGt (θ₀ T) : ℝ) := hCS₀
    have hratio' : |trG T ^ 2 / trG2 T - cT T * N T| ≤ C₃ * P.calE T * (cT T * N T) := by
      have := hratio T hT₃; simp only at this; rw [← mul_assoc] at this; exact this
    have htrG2 : 0 ≤ trG2 T := by rw [← hfr]; exact frobSq_nonneg _
    have hnp := nplus_ge_explicit hCS hxT.1 (mul_nonneg hθ0 (Nat.cast_nonneg _)) htrG2 hratio'
    -- c N − |cT − c| N ≤ cT N
    have hN0 : 0 ≤ N T := Nat.cast_nonneg _
    have hcd : c * N T - |cT T - c| * N T ≤ cT T * N T := by
      have h1 := mul_le_mul_of_nonneg_right (neg_abs_le (cT T - c)) hN0
      linarith [h1]
    simp only [hRdef, hxdef, hNdef] at hnp hcd hZ ⊢
    constructor <;> linarith [hZ.1, hZ.2, hnp, hcd]

/-- **Theorem D for L(s,χ), Thm-B line** (fixed λ, abstract): N₀ˢ(T,2T) ≥ (2c∞ − 1 − ε) N(T,2T) eventually. -/
theorem thmDChi_simple_abstract (Z : ZeroConfig) (κ : ℕ) {q : ℕ} (hq : 1 ≤ q) (cf : ℕ → ℂ)
    (P : Params) (hP : P.Valid) (hlam : P.lam < 1)
    (hRvM : RiemannVonMangoldtChi q Z)
    (aT bT JT trG trG2 : ℝ → ℝ)
    (hTr : TracesBoundsDChi P q aT bT JT trG trG2 (fun T => (Z.N T (2 * T) : ℝ)))
    {c : ℝ} (hc0 : 0 < c)
    (hc : Tendsto (fun T => cRatio (lam1q P q T) (aT T) (bT T) (JT T)) atTop (𝓝 c))
    (ha : ∀ᶠ T in atTop, 1 / 2 ≤ aT T ∧ aT T ≤ 1)
    (hBlock : ∀ᶠ T in atTop, BlockInputs Z (P.atD T) T)
    (θ₀ : ℝ → ℝ) (hTail : ∀ᶠ T in atTop, TailInputs Z (P.atD T) T (θ₀ T))
    (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop, (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop, Z.Gz (P.atD T) T = GpChi (P.atD T) κ q cf T)
    (hId : ∀ᶠ T in atTop, trGtildeChi (P.atD T) κ q cf T = trG T ∧
      trGtildeSqChi (P.atD T) κ q cf T = trG2 T ∧ (P.atD T).a T = aT T) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 * c - 1 - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.N0s T (2 * T) := by
  obtain ⟨R, hR, hev⟩ := thmDChi_BC_core Z κ hq cf P hP hlam hRvM aT bT JT trG trG2 hTr hc0 hc
    ha hBlock θ₀ hTail hθ₀ hNII hGzGp hId
  refine eps_form_of_isLittleO (err := fun T => 2 * R T) (hev.mono fun T h => ?_)
    (Eventually.of_forall fun T => Nat.cast_nonneg _) (hR.const_mul_left 2)
  linarith [h.1]

/-- **Theorem D for L(s,χ), Thm-C line** (fixed λ, abstract): N_d(T,2T) ≥ (c∞ − ε) N(T,2T) eventually. -/
theorem thmDChi_dist_abstract (Z : ZeroConfig) (κ : ℕ) {q : ℕ} (hq : 1 ≤ q) (cf : ℕ → ℂ)
    (P : Params) (hP : P.Valid) (hlam : P.lam < 1)
    (hRvM : RiemannVonMangoldtChi q Z)
    (aT bT JT trG trG2 : ℝ → ℝ)
    (hTr : TracesBoundsDChi P q aT bT JT trG trG2 (fun T => (Z.N T (2 * T) : ℝ)))
    {c : ℝ} (hc0 : 0 < c)
    (hc : Tendsto (fun T => cRatio (lam1q P q T) (aT T) (bT T) (JT T)) atTop (𝓝 c))
    (ha : ∀ᶠ T in atTop, 1 / 2 ≤ aT T ∧ aT T ≤ 1)
    (hBlock : ∀ᶠ T in atTop, BlockInputs Z (P.atD T) T)
    (θ₀ : ℝ → ℝ) (hTail : ∀ᶠ T in atTop, TailInputs Z (P.atD T) T (θ₀ T))
    (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop, (NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop, Z.Gz (P.atD T) T = GpChi (P.atD T) κ q cf T)
    (hId : ∀ᶠ T in atTop, trGtildeChi (P.atD T) κ q cf T = trG T ∧
      trGtildeSqChi (P.atD T) κ q cf T = trG2 T ∧ (P.atD T).a T = aT T) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (c - ε) * (Z.N T (2 * T) : ℝ) ≤ Z.Nd T (2 * T) := by
  obtain ⟨R, hR, hev⟩ := thmDChi_BC_core Z κ hq cf P hP hlam hRvM aT bT JT trG trG2 hTr hc0 hc
    ha hBlock θ₀ hTail hθ₀ hNII hGzGp hId
  exact eps_form_of_isLittleO (err := R) (hev.mono fun T h => h.2)
    (Eventually.of_forall fun T => Nat.cast_nonneg _) hR

end BC

end ThmDE
end Zeta23

end
