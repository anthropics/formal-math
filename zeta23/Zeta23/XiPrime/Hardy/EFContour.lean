/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Hardy/EFContour.lean — the two full-line contour identities of the W explicit formula
([XF′ Prop 9.1, Thm 9.2(a), (Z4)]).

  lminus_line_identity : (1/2π) ∫ [H(c+it) + H(1−c−it)]·(Lfn − L₂)(c+it) dt = ½ (H(0) + H(1)),
  w_full_line_identity : (1/2π) ∫ [H(c+it) + H(1−c−it)]·(L₂ + W′/W)(c+it) dt
                           = Σ'_{ρ ∈ wZeros} m_ρ H(ρ) + Σ_{ρ ∈ lowZerosW c t₀} ord_ρ(W) H(ρ) − (3/2)(H(0) + H(1)),
for 1 < c ≤ 5/4, H = WeilEF.Hfn k (k ∈ C²_c).  Pipeline: EFContour/Rectangle.lean (the identities at a fixed height:
pole-free argument principle for (Γℝ)⁻¹, (Γℝ)⁻¹∘(1−·), s(s−1), s(s−1)², Wreg) → EFContour/Limit.lean (the
integrand-generic R → ∞ passage) with: heights/horizontal bounds from Hardy/GoodHeightsW.lean (W) or from
the explicit Γℝ′/Γℝ log bounds (L₋); the fold symmetries L₋(1−s) = −L₋(s), F_𝒵(1−s) = −F_𝒵(s); summability of the zero
sum from hR.local_count via WeilEF.EF_zero_sum_summable_gen; and FullLine.zero_sum_limit_of for the windows.
The low zeros (|Im ρ| < t₀, 1−c < Re ρ < c, ρ ∉ {0,1}; REAL zeros of W included) form a fixed finite set.
-/
import Zeta23.XiPrime.Hardy.EFContour.Rectangle
import Zeta23.XiPrime.Hardy.EFContour.Limit
import Zeta23.XiPrime.Hardy.GoodHeightsW
import Zeta23.WeilEF.ZeroSummabilityGen

open Complex Set Filter Topology MeasureTheory
open Zeta23.WeilEF (Hfn)

noncomputable section

namespace Zeta23
namespace XiPrime

open Hardy Hardy.EFContour

/-! ## §1. L₋ := Lfn − L₂ through G = (Γℝ)⁻¹; symmetry; analyticity; bounds -/

namespace Hardy
namespace EFContour

/-- logDeriv (G∘(1−·)) s = −(G′/G)(1−s). -/
lemma logDeriv_invGammaℝ_comp_one_sub (s : ℂ) :
    logDeriv (fun z => invGammaℝ (1 - z)) s = -logDeriv invGammaℝ (1 - s) := by
  have h := logDeriv_comp (f := invGammaℝ) (g := fun z : ℂ => 1 - z) (x := s) (differentiable_invGammaℝ _)
    ((differentiableAt_const _).sub differentiableAt_id)
  rw [show (invGammaℝ ∘ fun z : ℂ => 1 - z) = fun z => invGammaℝ (1 - z) from rfl] at h
  rw [h, deriv_const_sub, deriv_id'']; ring

/-- L₂ = −½[(G′/G)(s) + (G′/G)(1−s)] wherever Γℝ(s), Γℝ(1−s) ≠ 0. -/
lemma L2_eq_G {s : ℂ} (h0 : Gammaℝ s ≠ 0) (h1 : Gammaℝ (1 - s) ≠ 0) :
    L2 s = -(1 / 2 : ℂ) * (logDeriv invGammaℝ s + logDeriv invGammaℝ (1 - s)) := by
  rw [L2, logDeriv_chiFE_eq h1 h0, logDeriv_Gammaℝ_one_sub_eq h1, logDeriv_invGammaℝ_comp_one_sub]; ring

/-- L₋ = −½(G′/G)(s) + ½(G′/G)(1−s) + 1/s + 1/(s−1). -/
lemma Lminus_eq_G {s : ℂ} (h0 : Gammaℝ s ≠ 0) (h1 : Gammaℝ (1 - s) ≠ 0) :
    Lfn s - L2 s = -(1 / 2 : ℂ) * logDeriv invGammaℝ s + (1 / 2 : ℂ) * logDeriv invGammaℝ (1 - s)
      + 1 / s + 1 / (s - 1) := by
  rw [Lfn, logDeriv_Gammaℝ_eq_neg h0, L2_eq_G h0 h1]; ring

/-- **L₋ is odd under s ↦ 1−s** (on the strip off the poles). -/
theorem Lminus_one_sub {s : ℂ} (h0 : Gammaℝ s ≠ 0) (h1 : Gammaℝ (1 - s) ≠ 0) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    Lfn (1 - s) - L2 (1 - s) = -(Lfn s - L2 s) := by
  have h1' : Gammaℝ (1 - (1 - s)) ≠ 0 := by rw [sub_sub_cancel]; exact h0
  rw [Lminus_eq_G h1 h1', Lminus_eq_G h0 h1, sub_sub_cancel]
  have : (1 : ℂ) - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  have : (1 : ℂ) - s - 1 ≠ 0 := by rw [sub_sub_cancel_left]; exact neg_ne_zero.mpr hs0
  have : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  field_simp
  ring

theorem Lfn_analyticAt {s : ℂ} (h0 : Gammaℝ s ≠ 0) (hs0 : s ≠ 0) (hs1 : s ≠ 1) : AnalyticAt ℂ Lfn s := by
  have e : Lfn = fun z => deriv Gammaℝ z / Gammaℝ z + 1 / z + 1 / (z - 1) := by
    funext z; rw [Lfn, logDeriv_apply]
  rw [e]
  have hG := analyticAt_Gammaℝ h0
  refine ((hG.deriv.div hG h0).add (analyticAt_const.div analyticAt_id hs0)).add
    (analyticAt_const.div (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr hs1))

theorem Lminus_analyticAt {s : ℂ} (hs : s ∈ stripReg) : AnalyticAt ℂ (fun z => Lfn z - L2 z) s :=
  (Lfn_analyticAt (Gammaℝ_ne_zero_of_re hs.1 hs.2.2.1) hs.2.2.1 hs.2.2.2).sub (L2_analyticAt_of_mem hs)

/-- ‖Γℝ′/Γℝ(u)‖ ≤ log(|Im u|+3) + 6 on −1/4 ≤ Re u ≤ 2, |Im u| ≥ 2 (shift once when Re u ≤ 0). -/
lemma norm_logDeriv_Gammaℝ_le_strip {u : ℂ} (hre : -1 / 4 ≤ u.re) (hre' : u.re ≤ 2) (him : 2 ≤ |u.im|) :
    ‖logDeriv Gammaℝ u‖ ≤ Real.log (|u.im| + 3) + 6 := by
  rcases lt_or_ge 0 u.re with hpos | hnp
  · have := ZeroCount.norm_logDeriv_Gammaℝ_le_log hpos (by linarith) him
    linarith
  · have hu : u.im ≠ 0 := by intro h; rw [h] at him; norm_num at him
    rw [logDeriv_Gammaℝ_shift hu]
    have h2 := ZeroCount.norm_logDeriv_Gammaℝ_le_log (s := u + 2) (by simp; linarith) (by simp; linarith)
      (by simpa using him)
    have hinv : ‖1 / u‖ ≤ 1 := by
      rw [norm_div, norm_one, div_le_one (norm_pos_iff.mpr (ne_zero_of_im_ne_zero hu))]
      exact le_trans (by linarith) (Complex.abs_im_le_norm u)
    calc ‖logDeriv Gammaℝ (u + 2) - 1 / u‖ ≤ ‖logDeriv Gammaℝ (u + 2)‖ + ‖1 / u‖ := norm_sub_le _ _
      _ ≤ (Real.log (|(u + 2).im| + 3) + 5) + 1 := add_le_add h2 hinv
      _ = Real.log (|u.im| + 3) + 6 := by simp; ring

/-- horizontal bound for L₋: ‖(Lfn − L₂)(s)‖ ≤ log(|Im s|+3) + 7 on 1−c ≤ Re s ≤ c, |Im s| ≥ 2. -/
lemma norm_Lminus_le {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 5 / 4) {s : ℂ} (hr1 : 1 - c ≤ s.re) (hr2 : s.re ≤ c)
    (him : 2 ≤ |s.im|) : ‖Lfn s - L2 s‖ ≤ Real.log (|s.im| + 3) + 7 := by
  have hs : s.im ≠ 0 := by intro h; rw [h] at him; norm_num at him
  have hs0 : s ≠ 0 := ne_zero_of_im_ne_zero hs
  have hs1 : s ≠ 1 := ne_one_of_im_ne_zero hs
  have h0 : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re (by linarith) hs0
  have h1 : Gammaℝ (1 - s) ≠ 0 := Gammaℝ_one_sub_ne_zero_of_re (by linarith) hs1
  rw [Lminus_eq_G h0 h1]
  have hG : ∀ u : ℂ, Gammaℝ u ≠ 0 → ‖logDeriv invGammaℝ u‖ = ‖logDeriv Gammaℝ u‖ := fun u hu => by
    rw [logDeriv_Gammaℝ_eq_neg hu, norm_neg]
  have hA : ‖logDeriv invGammaℝ s‖ ≤ Real.log (|s.im| + 3) + 6 := by
    rw [hG s h0]; exact norm_logDeriv_Gammaℝ_le_strip (by linarith) (by linarith) him
  have hB : ‖logDeriv invGammaℝ (1 - s)‖ ≤ Real.log (|s.im| + 3) + 6 := by
    rw [hG (1 - s) h1]
    have := norm_logDeriv_Gammaℝ_le_strip (u := 1 - s) (by simp; linarith) (by simp; linarith) (by simpa using him)
    simpa using this
  have hsnorm : 2 ≤ ‖s‖ := le_trans him (Complex.abs_im_le_norm s)
  have hs1norm : 2 ≤ ‖s - 1‖ := by
    have := Complex.abs_im_le_norm (s - 1); simp at this; linarith
  have hC : ‖1 / s‖ ≤ 1 / 2 := by
    rw [norm_div, norm_one]; exact div_le_div_of_nonneg_left zero_le_one (by norm_num) hsnorm
  have hD : ‖1 / (s - 1)‖ ≤ 1 / 2 := by
    rw [norm_div, norm_one]; exact div_le_div_of_nonneg_left zero_le_one (by norm_num) hs1norm
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  have hnhalf : ‖(-(1 / 2) : ℂ)‖ = 1 / 2 := by norm_num
  calc ‖-(1 / 2 : ℂ) * logDeriv invGammaℝ s + (1 / 2 : ℂ) * logDeriv invGammaℝ (1 - s) + 1 / s + 1 / (s - 1)‖
      ≤ ‖-(1 / 2 : ℂ) * logDeriv invGammaℝ s‖ + ‖(1 / 2 : ℂ) * logDeriv invGammaℝ (1 - s)‖ + ‖1 / s‖ + ‖1 / (s - 1)‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ (1 / 2) * (Real.log (|s.im| + 3) + 6) + (1 / 2) * (Real.log (|s.im| + 3) + 6) + 1 / 2 + 1 / 2 := by
        rw [norm_mul, norm_mul, hhalf, hnhalf]; gcongr
    _ = Real.log (|s.im| + 3) + 7 := by ring

end EFContour
end Hardy

/-! ## §2. The L₋ line identity -/

/-- **(1/2π) ∫ [H(c+it) + H(1−c−it)] · (Lfn − L₂)(c+it) dt = ½(H(0) + H(1))**, 1 < c ≤ 5/4. -/
theorem lminus_line_identity {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 5 / 4) {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) :
    Integrable (fun t : ℝ => (Hfn k ((c : ℂ) + t * I) + Hfn k (1 - c - t * I))
      * (Lfn ((c : ℂ) + t * I) - L2 ((c : ℂ) + t * I))) ∧
    (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, (Hfn k ((c : ℂ) + t * I) + Hfn k (1 - c - t * I))
        * (Lfn ((c : ℂ) + t * I) - L2 ((c : ℂ) + t * I)))
      = (1 / 2 : ℂ) * (Hfn k 0 + Hfn k 1) := by
  set F : ℂ → ℂ := fun s => Lfn s - L2 s with hF
  -- points of the two vertical lines are in stripReg
  have hline_mem : ∀ t : ℝ, ((c : ℂ) + t * I) ∈ stripReg := fun t =>
    ⟨by simp; linarith, by simp; linarith, fun h => by have := congrArg Complex.re h; simp at this; linarith,
      fun h => by have := congrArg Complex.re h; simp at this; linarith⟩
  have hl : Continuous fun t : ℝ => (c : ℂ) + t * I := by fun_prop
  have hFc : Continuous fun t : ℝ => F ((c : ℂ) + t * I) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    exact ContinuousAt.comp (f := fun t : ℝ => (c : ℂ) + t * I) (x := t)
      ((Lminus_analyticAt (hline_mem t)).continuousAt) hl.continuousAt
  have hsymm : ∀ t : ℝ, F (1 - ((c : ℂ) + t * I)) = -F ((c : ℂ) + t * I) := by
    intro t
    obtain ⟨ha, hb, h0, h1⟩ := hline_mem t
    exact Lminus_one_sub (Gammaℝ_ne_zero_of_re ha h0) (Gammaℝ_one_sub_ne_zero_of_re hb h1) h0 h1
  -- line bound: explicit for |t| ≥ 2, compactness for |t| ≤ 2
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ t ∈ Icc (-2 : ℝ) 2, ‖F ((c : ℂ) + t * I)‖ ≤ B :=
    isCompact_Icc.exists_bound_of_continuousOn hFc.continuousOn
  have hline : ∃ M : ℝ, ∀ t : ℝ, ‖F ((c : ℂ) + t * I)‖ ≤ M * Real.log (2 + |t|) := by
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    refine ⟨max (|B| / Real.log 2) 12, fun t => ?_⟩
    have hl2 : Real.log 2 ≤ Real.log (2 + |t|) := Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
    rcases le_or_gt |t| 2 with ht | ht
    · have h1 := hB t (abs_le.mp ht)
      calc ‖F ((c : ℂ) + t * I)‖ ≤ |B| := h1.trans (le_abs_self B)
        _ = (|B| / Real.log 2) * Real.log 2 := by field_simp
        _ ≤ max (|B| / Real.log 2) 12 * Real.log (2 + |t|) :=
            mul_le_mul (le_max_left _ _) hl2 hlog2.le (le_trans (by positivity) (le_max_left _ _))
    · have h := norm_Lminus_le hc1 hc2 (s := (c : ℂ) + t * I) (by simp; linarith) (by simp) (by simp; linarith)
      have hl3 : Real.log (|t| + 3) ≤ 2 * Real.log (2 + |t|) := by
        rw [← Real.log_rpow (by linarith [abs_nonneg t]), Real.rpow_two]
        exact Real.log_le_log (by linarith [abs_nonneg t]) (by nlinarith [abs_nonneg t])
      have hl4 : 1 ≤ Real.log (2 + |t|) := by
        rw [← Real.log_exp 1]
        exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
      simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, zero_add, mul_one, mul_zero, add_zero] at h
      calc ‖F ((c : ℂ) + t * I)‖ ≤ Real.log (|t| + 3) + 7 := h
        _ ≤ 12 * Real.log (2 + |t|) := by linarith
        _ ≤ max (|B| / Real.log 2) 12 * Real.log (2 + |t|) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
  -- heights R_j := j + 2 and the horizontal bound
  set R : ℕ → ℝ := fun j => (j : ℝ) + 2 with hRdef
  have hR : ∀ j : ℕ, (j : ℝ) + (2 : ℕ) ≤ R j ∧ R j ≤ (j : ℝ) + (2 : ℕ) + 1 := fun j => by
    simp only [hRdef, Nat.cast_ofNat]; constructor <;> linarith
  have hhor : ∀ j : ℕ, ∀ s : ℂ, (s.im = R j ∨ s.im = -R j) → 1 - c ≤ s.re → s.re ≤ c →
      ‖F s‖ ≤ 9 * (Real.log ((j : ℝ) + (2 : ℕ) + 3)) ^ 2 := by
    intro j s him hr1 hr2
    have habs : |s.im| = R j := by
      rcases him with h | h
      · rw [h, abs_of_nonneg]; simp [hRdef]; positivity
      · rw [h, abs_neg, abs_of_nonneg]; simp [hRdef]; positivity
    have h2 : 2 ≤ |s.im| := by rw [habs]; simp [hRdef]
    have h := norm_Lminus_le hc1 hc2 hr1 hr2 h2
    rw [habs] at h
    set Lg := Real.log ((j : ℝ) + (2 : ℕ) + 3) with hLg
    have hLg1 : 1 ≤ Lg := by
      rw [hLg, ← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) (by push_cast; linarith [Real.exp_one_lt_d9])
    have hl : Real.log (R j + 3) ≤ 2 * Lg := by
      rw [hLg, ← Real.log_rpow (by push_cast; positivity), Real.rpow_two]
      apply Real.log_le_log (by simp [hRdef]; positivity)
      simp only [hRdef]; push_cast; nlinarith
    calc ‖F s‖ ≤ Real.log (R j + 3) + 7 := h
      _ ≤ 2 * Lg + 7 * Lg ^ 2 := by nlinarith
      _ ≤ 9 * Lg ^ 2 := by nlinarith
  -- rectangle values (constant) and the limit
  have hE : ∀ j : ℕ, RectangleIntegral' (fun s => Hfn k s * F s) (((1 - c : ℝ) : ℂ) - R j * I) ((c : ℝ) + R j * I)
      = (1 / 2 : ℂ) * (Hfn k 0 + Hfn k 1) := fun j =>
    rect_Lminus hk hkc hc1 hc2 (R := R j) (by simp [hRdef]; positivity)
  exact full_line_of_rectangles (by linarith) (by linarith) hk hkc hFc hsymm hline (j₀ := 2) (by norm_num)
    (K := 9) (by norm_num) hR hhor hE tendsto_const_nhds

/-! ## §3. The low zeros of W and the W full-line identity -/

/-- the set of low zeros of W inside the contour strip: W(ρ) = 0, ρ ∉ {0,1}, |Im ρ| < t₀, 1−c < Re ρ < c
(REAL zeros included). -/
def lowZerosSet (c t₀ : ℝ) : Set ℂ :=
  {ρ : ℂ | hardyW ρ = 0 ∧ ρ ≠ 0 ∧ ρ ≠ 1 ∧ |ρ.im| < t₀ ∧ 1 - c < ρ.re ∧ ρ.re < c}

open Classical in
/-- the low zeros of W as a Finset (∅ if infinite — it is finite in every use, see finite_lowZerosSet). -/
def lowZerosW (c t₀ : ℝ) : Finset ℂ :=
  if h : (lowZerosSet c t₀).Finite then h.toFinset else ∅

theorem mem_lowZerosW {c t₀ : ℝ} {ρ : ℂ} (h : ρ ∈ lowZerosW c t₀) : |ρ.im| < t₀ ∧ 1 - c < ρ.re ∧ ρ.re < c := by
  unfold lowZerosW at h
  split_ifs at h with hfin
  · obtain ⟨-, -, -, h1, h2, h3⟩ := hfin.mem_toFinset.mp h
    exact ⟨h1, h2, h3⟩
  · simp at h

theorem mem_lowZerosW_iff {c t₀ : ℝ} (hfin : (lowZerosSet c t₀).Finite) {ρ : ℂ} :
    ρ ∈ lowZerosW c t₀ ↔ ρ ∈ lowZerosSet c t₀ := by
  unfold lowZerosW; rw [dif_pos hfin, Set.Finite.mem_toFinset]

/-- the low-zero set is finite for every 1 < c ≤ 5/4 and every t₀: it lies in the zero set of the analytic Wreg on the
closed rectangle [1−c, c] × [−T, T] (T = max t₀ 1), and Wreg 0 = ¼ ≠ 0. -/
theorem finite_lowZerosSet {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 5 / 4) (t₀ : ℝ) : (lowZerosSet c t₀).Finite := by
  set T : ℝ := max t₀ 1 with hT
  have hT0 : 0 < T := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hfA : AnalyticOnNhd ℂ Wreg (Rectangle (zc c T) (wc c T)) := fun s hs =>
    Wreg_analyticAt (re_bounds_of_mem hc1 hc2 hT0 hs).1 (re_bounds_of_mem hc1 hc2 hT0 hs).2
  have hfin := Zeta23.Analytic.finite_zeros_rectangle hfA (zero_mem_rect hc1 hc2 hT0) (by rw [Wreg_zero]; norm_num)
  refine hfin.subset ?_
  rintro ρ ⟨h0, hne0, hne1, him, hr1, hr2⟩
  have hρQ : ρ ∈ Rectangle (zc c T) (wc c T) :=
    (mem_rect_iff (by linarith) hT0.le ρ).mpr ⟨⟨hr1.le, hr2.le⟩,
      by linarith [(abs_lt.mp him).1, le_max_left t₀ 1], by linarith [(abs_lt.mp him).2, le_max_left t₀ 1]⟩
  refine ⟨hρQ, ?_⟩
  rw [Set.mem_preimage, Set.mem_singleton_iff,
    Wreg_eq_zero_iff ⟨(re_bounds_of_mem hc1 hc2 hT0 hρQ).1, (re_bounds_of_mem hc1 hc2 hT0 hρQ).2, hne0, hne1⟩]
  exact h0

theorem mem_lowZerosW_iff' {c t₀ : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 5 / 4) {ρ : ℂ} :
    ρ ∈ lowZerosW c t₀ ↔ ρ ∈ lowZerosSet c t₀ := mem_lowZerosW_iff (finite_lowZerosSet hc1 hc2 t₀)

/-- re-indexing good heights into a sequence R_j ∈ [j+j₁, j+j₁+1], j₁ ≥ 1, R_j > t₀. -/
lemma exists_heightsW {t₀ : ℝ}
    (hGH : ∃ C : ℝ, 0 < C ∧ ∃ j₀ : ℕ, t₀ + 1 ≤ j₀ ∧ ∀ j : ℕ, j₀ ≤ j → ∃ R : ℝ, (j : ℝ) ≤ R ∧ R ≤ (j : ℝ) + 1 ∧
      ∀ s : ℂ, (s.im = R ∨ s.im = -R) → -1 ≤ s.re → s.re ≤ 2 →
        hardyW s ≠ 0 ∧ ‖L2 s + logDeriv hardyW s‖ ≤ C * (Real.log ((j : ℝ) + 3)) ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ j₁ : ℕ, 1 ≤ j₁ ∧ t₀ < j₁ ∧ ∃ R : ℕ → ℝ, ∀ j : ℕ,
      (j : ℝ) + j₁ ≤ R j ∧ R j ≤ (j : ℝ) + j₁ + 1 ∧
      ∀ s : ℂ, (s.im = R j ∨ s.im = -R j) → -1 ≤ s.re → s.re ≤ 2 →
        hardyW s ≠ 0 ∧ ‖L2 s + logDeriv hardyW s‖ ≤ C * (Real.log ((j : ℝ) + j₁ + 3)) ^ 2 := by
  obtain ⟨C, hC, j₀, ht₀, h⟩ := hGH
  have hex : ∀ j : ℕ, ∃ R : ℝ, ((j + (j₀ + 1) : ℕ) : ℝ) ≤ R ∧ R ≤ ((j + (j₀ + 1) : ℕ) : ℝ) + 1 ∧
      ∀ s : ℂ, (s.im = R ∨ s.im = -R) → -1 ≤ s.re → s.re ≤ 2 →
        hardyW s ≠ 0 ∧ ‖L2 s + logDeriv hardyW s‖ ≤ C * (Real.log (((j + (j₀ + 1) : ℕ) : ℝ) + 3)) ^ 2 :=
    fun j => h (j + (j₀ + 1)) (by omega)
  refine ⟨C, hC, j₀ + 1, by omega, by push_cast; linarith, fun j => (hex j).choose, fun j => ?_⟩
  obtain ⟨hs1, hs2, hs3⟩ := (hex j).choose_spec
  have e : ((j + (j₀ + 1) : ℕ) : ℝ) = (j : ℝ) + ((j₀ + 1 : ℕ) : ℝ) := by push_cast; ring
  refine ⟨by rw [← e]; exact hs1, by rw [← e]; exact hs2, fun s him h1 h2 => ?_⟩
  rw [← e]
  exact hs3 s him h1 h2

/-- **The W full-line identity** [XF′ Prop 9.1 / (Z4)]. -/
theorem w_full_line_identity {t₀ : ℝ} (hZ : WZerosInStrip t₀) (hs : WSeam t₀)
    (hR : RiemannVonMangoldt (wZeros hZ hs))
    {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 5 / 4)
    (hWc : ∀ s : ℂ, s.re = c → |s.im| < t₀ → hardyW s ≠ 0)
    (hWc' : ∀ s : ℂ, s.re = 1 - c → |s.im| < t₀ → hardyW s ≠ 0)
    (hline : ∃ M : ℝ, ∀ t : ℝ, ‖L2 ((c : ℂ) + t * I) + logDeriv hardyW ((c : ℂ) + t * I)‖ ≤ M * Real.log (2 + |t|))
    {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    Summable (fun ρ : (wZeros hZ hs).carrier => (wMult (ρ : ℂ) : ℂ) * Hfn k ρ) ∧
    (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, (Hfn k ((c : ℂ) + t * I) + Hfn k (1 - c - t * I))
        * (L2 ((c : ℂ) + t * I) + logDeriv hardyW ((c : ℂ) + t * I)))
      = (∑' ρ : (wZeros hZ hs).carrier, (wMult (ρ : ℂ) : ℂ) * Hfn k ρ)
        + (∑ ρ ∈ lowZerosW c t₀, (analyticOrderNatAt hardyW ρ : ℂ) * Hfn k ρ)
        - (3 / 2 : ℂ) * (Hfn k 0 + Hfn k 1) := by
  classical
  have ht₀ : 0 < t₀ := hs.pos
  set F : ℂ → ℂ := fun s => L2 s + logDeriv hardyW s with hF
  set Zc : ZeroConfig := wZeros hZ hs with hZc
  -- summability of the zero sum from the local count
  obtain ⟨A₀, hA₀, hloc⟩ := hR.local_count
  have hsum : Summable (fun ρ : Zc.carrier => (wMult (ρ : ℂ) : ℂ) * Hfn k ρ) :=
    Zeta23.WeilEF.EF_zero_sum_summable_gen Zc hA₀ hloc hk hkc
  refine ⟨hsum, ?_⟩
  -- W ≠ 0 on the two vertical lines (any height)
  have hvert : ∀ s : ℂ, (s.re = 1 - c ∨ s.re = c) → hardyW s ≠ 0 := by
    intro s hre h0
    rcases lt_or_ge |s.im| t₀ with hlt | hge
    · rcases hre with h | h
      · exact hWc' s h hlt h0
      · exact hWc s h hlt h0
    · have := hZ s h0 hge
      rcases hre with h | h <;> rw [h] at this <;> linarith [this.1, this.2]
  have hline_mem : ∀ t : ℝ, ((c : ℂ) + t * I) ∈ stripReg := fun t =>
    ⟨by simp; linarith, by simp; linarith, fun h => by have := congrArg Complex.re h; simp at this; linarith,
      fun h => by have := congrArg Complex.re h; simp at this; linarith⟩
  have hline_mem' : ∀ t : ℝ, ((1 : ℂ) - ((c : ℂ) + t * I)) ∈ stripReg := fun t =>
    ⟨by simp; linarith, by simp; linarith, fun h => by have := congrArg Complex.re h; simp at this; linarith,
      fun h => by have := congrArg Complex.re h; simp at this; linarith⟩
  -- F is analytic at every point of both lines
  have hFan : ∀ s : ℂ, s ∈ stripReg → hardyW s ≠ 0 → AnalyticAt ℂ F s := by
    intro s hsR hW
    have ha := hardyW_analyticAt_of_mem hsR
    have e : F = fun z => L2 z + deriv hardyW z / hardyW z := by funext z; simp only [hF, logDeriv_apply]
    rw [e]
    exact (L2_analyticAt_of_mem hsR).add (ha.deriv.div ha hW)
  have hl : Continuous fun t : ℝ => (c : ℂ) + t * I := by fun_prop
  have hl' : Continuous fun t : ℝ => (1 : ℂ) - ((c : ℂ) + t * I) := by fun_prop
  have hFc : Continuous fun t : ℝ => F ((c : ℂ) + t * I) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    exact ContinuousAt.comp (f := fun t : ℝ => (c : ℂ) + t * I) (x := t)
      (hFan _ (hline_mem t) (hvert _ (Or.inr (by simp)))).continuousAt hl.continuousAt
  have hFc' : Continuous fun t : ℝ => F (1 - ((c : ℂ) + t * I)) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    exact ContinuousAt.comp (f := fun t : ℝ => (1 : ℂ) - ((c : ℂ) + t * I)) (x := t)
      (hFan _ (hline_mem' t) (hvert _ (Or.inl (by simp)))).continuousAt hl'.continuousAt
  -- the fold symmetry on the line, extended to t = 0 by continuity
  have hsymm : ∀ t : ℝ, F (1 - ((c : ℂ) + t * I)) = -F ((c : ℂ) + t * I) := by
    have heq : (fun t : ℝ => F (1 - ((c : ℂ) + t * I))) = fun t : ℝ => -F ((c : ℂ) + t * I) := by
      refine Continuous.ext_on (dense_compl_singleton (0 : ℝ)) hFc' hFc.neg (fun t ht => ?_)
      have him : ((c : ℂ) + t * I).im ≠ 0 := by simpa using ht
      exact L2_add_logDeriv_hardyW_one_sub him (hvert _ (Or.inr (by simp)))
    intro t; exact congr_fun heq t
  -- good heights
  obtain ⟨C, hC, j₁, hj₁, hj₁t, R, hRj⟩ := exists_heightsW (hardyW_good_heights hZ hs)
  have hRt : ∀ j : ℕ, t₀ < R j := fun j => by
    have := (hRj j).1; have : (0:ℝ) ≤ j := Nat.cast_nonneg j; linarith
  have hR0 : ∀ j : ℕ, 0 < R j := fun j => lt_trans ht₀ (hRt j)
  have hRge : ∀ j : ℕ, (j : ℝ) ≤ R j := fun j => by have := (hRj j).1; have : (0:ℝ) ≤ j₁ := Nat.cast_nonneg j₁; linarith
  have hRmono : Monotone R := by
    intro i j hij
    rcases hij.eq_or_lt with h | h
    · rw [h]
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      linarith [(hRj i).2.1, (hRj j).1]
  have hhor : ∀ j : ℕ, ∀ s : ℂ, (s.im = R j ∨ s.im = -R j) → 1 - c ≤ s.re → s.re ≤ c →
      ‖F s‖ ≤ C * (Real.log ((j : ℝ) + j₁ + 3)) ^ 2 := fun j s him h1 h2 =>
    ((hRj j).2.2 s him (by linarith) (by linarith)).2
  -- W ≠ 0 on the border of every rectangle
  have hWb : ∀ j : ℕ, ∀ s ∈ RectangleBorder (zc c (R j)) (wc c (R j)), hardyW s ≠ 0 := by
    intro j s hsb
    rcases border_cases hsb with h | h | h | h
    · exact hvert s (Or.inl h)
    · exact hvert s (Or.inr h)
    · obtain ⟨⟨h1, h2⟩, -⟩ := (mem_rect_iff (by linarith) (hR0 j).le s).mp (rectangleBorder_subset_rectangle _ _ hsb)
      exact ((hRj j).2.2 s (Or.inr h) (by linarith) (by linarith)).1
    · obtain ⟨⟨h1, h2⟩, -⟩ := (mem_rect_iff (by linarith) (hR0 j).le s).mp (rectangleBorder_subset_rectangle _ _ hsb)
      exact ((hRj j).2.2 s (Or.inl h) (by linarith) (by linarith)).1
  -- the rectangle identities
  have hrect : ∀ j : ℕ, ∃ Z : Finset ℂ,
      ((Z : Set ℂ) = {ρ : ℂ | ρ ∈ Rectangle (zc c (R j)) (wc c (R j)) ∧ ρ ≠ 0 ∧ ρ ≠ 1 ∧ hardyW ρ = 0}) ∧
      RectangleIntegral' (fun s => Hfn k s * F s) (zc c (R j)) (wc c (R j))
        = (∑ ρ ∈ Z, (analyticOrderNatAt hardyW ρ : ℂ) * Hfn k ρ) - (3 / 2 : ℂ) * (Hfn k 0 + Hfn k 1) :=
    fun j => rect_FZ hk hkc hc1 hc2 (hR0 j) (hWb j)
  choose Z hZc hE using hrect
  have hmemZ : ∀ j ρ, ρ ∈ Z j ↔ ρ ∈ Rectangle (zc c (R j)) (wc c (R j)) ∧ ρ ≠ 0 ∧ ρ ≠ 1 ∧ hardyW ρ = 0 := by
    intro j ρ; rw [← Finset.mem_coe, hZc j]; rfl
  -- the low zeros: finite (inside Z 0) and described by lowZerosSet
  have hlow_sub : ∀ j, lowZerosSet c t₀ ⊆ (Z j : Set ℂ) := by
    intro j ρ hρ
    obtain ⟨h0, hne0, hne1, him, hr1, hr2⟩ := hρ
    rw [Finset.mem_coe, hmemZ]
    refine ⟨(mem_rect_iff (by linarith) (hR0 j).le ρ).mpr ⟨⟨hr1.le, hr2.le⟩, ?_, ?_⟩, hne0, hne1, h0⟩
    · linarith [(abs_lt.mp him).1, hRt j]
    · linarith [(abs_lt.mp him).2, hRt j]
  have hfin : (lowZerosSet c t₀).Finite := (Z 0).finite_toSet.subset (hlow_sub 0)
  -- splitting Z j into the configuration window and the low zeros
  set Zbig : ℕ → Finset ℂ := fun j => (Z j).filter (fun ρ => t₀ ≤ |ρ.im|) with hZbig
  have hZbig_coe : ∀ j : ℕ, ((Zbig j : Finset ℂ) : Set ℂ) = {ρ : ℂ | ρ ∈ Zc.carrier ∧ -R j < ρ.im ∧ ρ.im < R j} := by
    intro j
    ext ρ
    rw [Finset.mem_coe, hZbig, Finset.mem_filter, hmemZ, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨hρQ, h0, h1, hW0⟩, him⟩
      have himne : ρ.im ≠ 0 := by intro h; rw [h, abs_zero] at him; linarith
      obtain ⟨-, hi1, hi2⟩ := (mem_rect_iff (by linarith) (hR0 j).le ρ).mp hρQ
      refine ⟨⟨⟨hW0, himne⟩, him⟩, lt_of_le_of_ne hi1 ?_, lt_of_le_of_ne hi2 ?_⟩
      · intro h
        have hb : ρ ∈ RectangleBorder (zc c (R j)) (wc c (R j)) := by
          refine Or.inl (Or.inl (Or.inl ⟨?_, ?_⟩))
          · obtain ⟨⟨a, b⟩, -⟩ := (mem_rect_iff (by linarith) (hR0 j).le ρ).mp hρQ
            simp only [zc_re, wc_re]; exact Set.mem_uIcc.mpr (Or.inl ⟨a, b⟩)
          · simp [← h]
        exact hWb j ρ hb hW0
      · intro h
        have hb : ρ ∈ RectangleBorder (zc c (R j)) (wc c (R j)) := by
          refine Or.inl (Or.inr ⟨?_, ?_⟩)
          · obtain ⟨⟨a, b⟩, -⟩ := (mem_rect_iff (by linarith) (hR0 j).le ρ).mp hρQ
            simp only [zc_re, wc_re]; exact Set.mem_uIcc.mpr (Or.inl ⟨a, b⟩)
          · simp [h]
        exact hWb j ρ hb hW0
    · rintro ⟨⟨⟨hW0, himne⟩, him⟩, hi1, hi2⟩
      have hstrip := hZ ρ hW0 him
      refine ⟨⟨(mem_rect_iff (by linarith) (hR0 j).le ρ).mpr ⟨⟨by linarith [hstrip.1], by linarith [hstrip.2]⟩,
        hi1.le, hi2.le⟩, ne_zero_of_im_ne_zero himne, ne_one_of_im_ne_zero himne, hW0⟩, him⟩
  have hsplit : ∀ j : ℕ, ∑ ρ ∈ Z j, (analyticOrderNatAt hardyW ρ : ℂ) * Hfn k ρ
      = (∑ ρ ∈ Zbig j, (analyticOrderNatAt hardyW ρ : ℂ) * Hfn k ρ)
        + ∑ ρ ∈ lowZerosW c t₀, (analyticOrderNatAt hardyW ρ : ℂ) * Hfn k ρ := by
    intro j
    have hlow_eq : lowZerosW c t₀ = (Z j).filter (fun ρ => ¬ t₀ ≤ |ρ.im|) := by
      ext ρ
      rw [mem_lowZerosW_iff hfin, Finset.mem_filter, hmemZ]
      constructor
      · intro hρ
        have := hlow_sub j hρ
        rw [Finset.mem_coe, hmemZ] at this
        exact ⟨this, not_le.mpr hρ.2.2.2.1⟩
      · rintro ⟨⟨hρQ, h0, h1, hW0⟩, him⟩
        obtain ⟨⟨hr1, hr2⟩, -⟩ := (mem_rect_iff (by linarith) (hR0 j).le ρ).mp hρQ
        refine ⟨hW0, h0, h1, not_le.mp him, lt_of_le_of_ne hr1 ?_, lt_of_le_of_ne hr2 ?_⟩
        · intro h; exact hvert ρ (Or.inl h.symm) hW0
        · intro h; exact hvert ρ (Or.inr h) hW0
    rw [hlow_eq, hZbig]
    exact (Finset.sum_filter_add_sum_filter_not (Z j) (fun ρ => t₀ ≤ |ρ.im|) _).symm
  -- the limit of the big part
  have hZlim := zero_sum_limit_of (Zset := Zc.carrier) (fun ρ => (wMult ρ : ℂ) * Hfn k ρ) hsum hRmono hRge hZbig_coe
  have hmult : ∀ ρ, (analyticOrderNatAt hardyW ρ : ℂ) = (wMult ρ : ℂ) := fun ρ => by rw [analyticOrderNatAt_hardyW]
  have hElim : Tendsto (fun j => (∑ ρ ∈ Z j, (analyticOrderNatAt hardyW ρ : ℂ) * Hfn k ρ) - (3 / 2 : ℂ) * (Hfn k 0 + Hfn k 1))
      atTop (𝓝 ((∑' ρ : Zc.carrier, (wMult (ρ : ℂ) : ℂ) * Hfn k ρ)
        + (∑ ρ ∈ lowZerosW c t₀, (analyticOrderNatAt hardyW ρ : ℂ) * Hfn k ρ) - (3 / 2 : ℂ) * (Hfn k 0 + Hfn k 1))) := by
    have h1 : Tendsto (fun j => ∑ ρ ∈ Zbig j, (analyticOrderNatAt hardyW ρ : ℂ) * Hfn k ρ) atTop
        (𝓝 (∑' ρ : Zc.carrier, (wMult (ρ : ℂ) : ℂ) * Hfn k ρ)) := by
      refine hZlim.congr fun j => Finset.sum_congr rfl fun ρ _ => by rw [hmult]
    have := (h1.add_const (∑ ρ ∈ lowZerosW c t₀, (analyticOrderNatAt hardyW ρ : ℂ) * Hfn k ρ)).sub_const
      ((3 / 2 : ℂ) * (Hfn k 0 + Hfn k 1))
    refine this.congr fun j => ?_
    rw [hsplit j]
  have hE' : ∀ j : ℕ, RectangleIntegral' (fun s => Hfn k s * F s) (((1 - c : ℝ) : ℂ) - R j * I) ((c : ℝ) + R j * I)
      = (∑ ρ ∈ Z j, (analyticOrderNatAt hardyW ρ : ℂ) * Hfn k ρ) - (3 / 2 : ℂ) * (Hfn k 0 + Hfn k 1) :=
    fun j => hE j
  exact (full_line_of_rectangles (by linarith) (by linarith) hk hkc hFc hsymm hline hj₁ hC.le
    (fun j => ⟨(hRj j).1, (hRj j).2.1⟩) hhor hE' hElim).2

end XiPrime
end Zeta23

end
