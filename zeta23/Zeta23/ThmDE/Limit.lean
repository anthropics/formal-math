/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmDE/Limit.lean — [thm:E] "Theorem D holds likewise" — the
λ_{1,χ} → λ limit and the generic concrete-ratio convergence for the χ D-window.
-/
import Zeta23.ThmD.Limit
import Zeta23.ThmE.AssemblyQ

open Filter Real Topology

noncomputable section

namespace Zeta23
namespace ThmDE

/-- λ_{1,χ}(T) → λ (q fixed). -/
theorem tendsto_lam1q {P : Params} (hP : P.Valid) {q : ℕ} (hq : 1 ≤ q) :
    Tendsto (fun T => ThmE.lam1q P q T) atTop (𝓝 P.lam) := by
  have hlam := hP.lam_pos
  have hl := Assembly.tendsto_l_atTop
  have hbound : ∀ᶠ T in atTop, P.lam - P.lam * ThmE.cq q / l T ≤ ThmE.lam1q P q T
      ∧ ThmE.lam1q P q T ≤ P.lam := by
    filter_upwards [Assembly.eventually_l_pos, eventually_gt_atTop (0:ℝ)] with T hlT hT
    exact ⟨by linarith [ThmE.sub_lam1q_le P hq hT hlam.le hlT],
      ThmE.lam1q_le P hq hT hlam.le hlT⟩
  have hlow : Tendsto (fun T => P.lam - P.lam * ThmE.cq q / l T) atTop (𝓝 P.lam) := by
    have h0 : Tendsto (fun T => P.lam * ThmE.cq q / l T) atTop (𝓝 0) :=
      Tendsto.div_atTop tendsto_const_nhds hl
    have := tendsto_const_nhds (x := P.lam) (f := atTop (α := ℝ)) |>.sub h0
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
    (hbound.mono fun T h => h.1) (hbound.mono fun T h => h.2)

/-- the χ concrete-ratio limit, parametric in the window-moment limits. -/
theorem tendsto_cRatio_concreteChi {P : Params} (hP : P.Valid) {q : ℕ} (hq : 1 ≤ q)
    (aT bT JT : ℝ → ℝ)
    (ha : Tendsto aT atTop (𝓝 (ThmD.aStar P.lam)))
    (hb : Tendsto bT atTop (𝓝 (ThmD.bStar P.lam)))
    (hJ : Tendsto JT atTop (𝓝 (ThmD.jStar P.lam))) :
    Tendsto (fun T => ThmD.cRatio (ThmE.lam1q P q T) (aT T) (bT T) (JT T)) atTop
      (𝓝 (ThmD.cStar P.lam)) :=
  ThmD.tendsto_cRatio_of hP.lam_pos hP.lam_le_one (tendsto_lam1q hP hq) ha hb hJ

end ThmDE
end Zeta23
