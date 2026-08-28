/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/XiPrime/Window/Quartic.lean — the quartic-window ratio limit, modulo the three window-moment estimates
(Zeta23/XiPrime/QuarticWindow/Moments.lean).

Shapes: for φ_V := P.phiV vQuartic T (Defs), with av/bv/gv the AdmWindow data
(Zeta23/ThmD/WindowCore.lean),
  aV_quartic_close : ∀ᶠ T, |av φ_V L − 2777/3000|     ≤ C·w/L,
  bV_quartic_close : ∀ᶠ T, |bv φ_V L − 518783/600000|  ≤ C·w/L,
  gV_quartic_close : ∀ᶠ T, ∀ y ∈ [0,L], |gv φ_V y − L·(v⋆v)(y/L)| ≤ C·w,   + gv φ_V continuous eventually.
This file turns ANY data satisfying those shapes into  cRatio(λ₁(T); a_T, b_T, J_T) → c_λ(vQuartic; D)
(tendsto_cRatio_quartic_of), and instantiates it with the estimates of QuarticWindow/Moments.lean:
tendsto_cRatio_quartic / tendsto_cRatio_quartic_D1, in the (P.atV vQuartic T).a/.b/.g spelling that
coeffMoments_atV consumes.
-/
import Zeta23.XiPrime.Window
import Zeta23.XiPrime.QuarticWindow.Moments
import Zeta23.XiPrime.QuarticWindow.Params

open Set Filter Topology

noncomputable section

namespace Zeta23
namespace XiPrime

/-- **quartic-window ratio limit from the window-moment estimates.** -/
theorem tendsto_cRatio_quartic_of {P : Params} (hP : P.Valid) {D : ℝ → ℝ}
    (hD : ContinuousOn D (Icc 0 1)) (hD0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ D x)
    {aT bT : ℝ → ℝ} {g : ℝ → ℝ → ℝ} {Ca Cb Cg : ℝ}
    (ha : ∀ᶠ T in atTop, |aT T - 2777 / 3000| ≤ Ca * P.w / P.L T)
    (hb : ∀ᶠ T in atTop, |bT T - 518783 / 600000| ≤ Cb * P.w / P.L T)
    (hgc : ∀ᶠ T in atTop, Continuous (g T))
    (hg : ∀ᶠ T in atTop, ∀ y ∈ Icc (0:ℝ) (P.L T),
      |g T y - P.L T * vConv vQuartic (y / P.L T)| ≤ Cg * P.w) :
    Tendsto (fun T => ThmD.cRatio (P.lam1 T) (aT T) (bT T)
      (2 / P.L T ^ 3 * l T * ∫ y in (0:ℝ)..P.L T, (D (y / l T) * g T y))) atTop
      (𝓝 (cWin D P.lam vQuartic)) := by
  have haT : Tendsto aT atTop (𝓝 (∫ s in (-(1:ℝ)/2)..(1/2), vQuartic s)) := by
    rw [integral_vQuartic]; exact ThmD.tendsto_of_close hP.lam_pos ha
  have hbT : Tendsto bT atTop (𝓝 (∫ s in (-(1:ℝ)/2)..(1/2), vQuartic s ^ 2)) := by
    rw [integral_vQuartic_sq]; exact ThmD.tendsto_of_close hP.lam_pos hb
  have hJ := tendsto_JT_of_autocorr_close (v := vQuartic) hP hD continuous_vQuartic hgc hg
  refine tendsto_cRatio_cWin hP.lam_pos (ThmD.tendsto_lam1 hP.lam_pos) haT hbT hJ ?_
  exact cWin_denom_pos (by rw [integral_vQuartic_sq]; norm_num)
    (jWin_nonneg hD0 (fun _ hs => vQuartic_nonneg_on hs) hP.lam_pos.le hP.lam_le_one) hP.lam_pos.le

/-- positivity of the limit constant (Endgame/CoeffMoments' hc0) for any D ≥ 0 on [0,1]. -/
theorem cWin_vQuartic_pos {D : ℝ → ℝ} (hD0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ D x) {lam : ℝ} (h0 : 0 < lam)
    (h1 : lam ≤ 1) : 0 < cWin D lam vQuartic :=
  cWin_pos (by rw [integral_vQuartic]; norm_num) (by rw [integral_vQuartic_sq]; norm_num)
    (jWin_nonneg hD0 (fun _ hs => vQuartic_nonneg_on hs) h0.le h1) h0

/-! ## instantiation with the window-moment estimates (see Zeta23/XiPrime/QuarticWindow/{Moments,Params}.lean) -/

section K3
variable {P : Params}

lemma atVQ_g (hP : P.Valid) (T : ℝ) : (P.atV vQuartic T).g T = AdmWindow.gv (P.phiV vQuartic T) := by
  show AdmWindow.gv ((P.atV vQuartic T).phi T) = _
  rw [Params.atV_phi_valid T hP vQuartic_even]

/-- **The quartic-window ratio limit** (the `hc` hypothesis of `coeffMoments_atV`, with `JD` unfolded):
cRatio(λ₁(T); a_T, b_T, J_T) → c_λ(vQuartic; D) for the data of P.atV vQuartic, any continuous D ≥ 0 on [0,1]. -/
theorem tendsto_cRatio_quartic (hP : P.Valid) {D : ℝ → ℝ} (hD : ContinuousOn D (Icc 0 1))
    (hD0 : ∀ x ∈ Icc (0:ℝ) 1, 0 ≤ D x) :
    Tendsto (fun T => ThmD.cRatio (P.lam1 T) ((P.atV vQuartic T).a T) ((P.atV vQuartic T).b T)
      (2 / P.L T ^ 3 * l T * ∫ y in (0:ℝ)..P.L T, (D (y / l T) * (P.atV vQuartic T).g T y))) atTop
      (𝓝 (cWin D P.lam vQuartic)) := by
  have hev := eventually_w8 hP
  have ha : ∀ᶠ T in atTop, |(P.atV vQuartic T).a T - 2777 / 3000| ≤ 2 * P.w / P.L T := by
    filter_upwards [hev] with T hT
    rw [Params.atV_a T hP vQuartic_even]; exact aV_quartic_close hP hT
  have hb : ∀ᶠ T in atTop, |(P.atV vQuartic T).b T - 518783 / 600000| ≤ 2 * P.w / P.L T := by
    filter_upwards [hev] with T hT
    rw [Params.atV_b T hP vQuartic_even]; exact bV_quartic_close hP hT
  have hgc : ∀ᶠ T in atTop, Continuous ((P.atV vQuartic T).g T) := by
    filter_upwards [hev] with T hT
    rw [atVQ_g hP T]; exact gV_quartic_continuous hP hT
  have hg : ∀ᶠ T in atTop, ∀ y ∈ Icc (0:ℝ) (P.L T),
      |(P.atV vQuartic T).g T y - P.L T * vConv vQuartic (y / P.L T)| ≤ 4 * P.w := by
    filter_upwards [hev] with T hT y hy
    rw [atVQ_g hP T]; exact gV_quartic_close_at hP hT hy
  exact tendsto_cRatio_quartic_of (g := fun T => (P.atV vQuartic T).g T) hP hD hD0 ha hb hgc hg

/-- the D₁ instance, with the positivity the endgame wants. -/
theorem tendsto_cRatio_quartic_D1 (hP : P.Valid) :
    Tendsto (fun T => ThmD.cRatio (P.lam1 T) ((P.atV vQuartic T).a T) ((P.atV vQuartic T).b T)
      (2 / P.L T ^ 3 * l T * ∫ y in (0:ℝ)..P.L T, (D1 (y / l T) * (P.atV vQuartic T).g T y))) atTop
      (𝓝 (cWin D1 P.lam vQuartic)) :=
  tendsto_cRatio_quartic hP (continuousOn_D1 _) (fun _ hx => D1_nonneg hx.1)

end K3

end XiPrime
end Zeta23
