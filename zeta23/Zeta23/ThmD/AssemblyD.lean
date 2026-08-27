/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmD/AssemblyD.lean — the parametric fixed-T core and the TracesBoundsD interface
(produced by Traces.lean/Concrete.lean, consumed by Endgame.lean).

§6 of the paper with the window-general ratio constant ([eq:ratio-general]):
  (tr G~)²/tr G~² = (λ₁ a²/(b + λ₁² J)) · N(T,2T) · (1 + O(E_T)),
replacing F(λ₁) (the flat-top case a=b→1, J→1/3).  The ONLY place Assembly.lean's fixed-T §6
endgame uses the flat top is the literal (1/λ₁ + λ₁/3) in N0star_lower_H's hfr hypothesis;
the abstract-constant copy below is proved by the same argument.
-/
import Zeta23.Assembly
import Zeta23.ThmD.Functional

noncomputable section

open Real

namespace Zeta23
namespace ThmD

/-- the window-general ratio constant of [eq:ratio-general]: c(λ₁; a, b, J) := λ₁a²/(b + λ₁²J).
Flat top (a = b = 1, J = 1/3): c = F(λ₁); Montgomery–Taylor window: c → cStar λ + O(w/L + 1/l). -/
def cRatio (lam1 a b J : ℝ) : ℝ := lam1 * a ^ 2 / (b + lam1 ^ 2 * J)

/-- flat-top sanity: cRatio λ₁ 1 1 (1/3) = F(λ₁). -/
theorem cRatio_flat (lam1 : ℝ) : cRatio lam1 1 1 (1/3) = Ffun lam1 := by
  unfold cRatio Ffun
  ring_nf

/-! ### The fixed-T endgame with an abstract constant (parametric copy of
Assembly.lean's N0star_lower_H; same proof) -/

/-- §6, Thm A-line, window-general: with cinv in the role of 1/λ₁ + λ₁/3 = 1/F(λ₁):
if 4trG^ − ‖G^‖² − 2N − 3N(I′∖I) − B(4+2‖G^‖+B) ≤ N₀*, |trG^ − N| ≤ R₁, ‖G^‖² ≤ cinv·N + R₂,
then (2 − cinv)N − [4R₁ + R₂ + 3NII + B(4 + 2√(cinv·N + R₂) + B)] ≤ N₀*. -/
theorem N0star_lower_c
    {N0star N NII trGh frGh B cinv R₁ R₂ : ℝ} (hB : 0 ≤ B)
    (h0 : 4 * trGh - frGh - 2 * N - 3 * NII - B * (4 + 2 * Real.sqrt frGh + B) ≤ N0star)
    (htr : |trGh - N| ≤ R₁) (hfr : frGh ≤ cinv * N + R₂) :
    (2 - cinv) * N - (4 * R₁ + R₂ + 3 * NII
        + B * (4 + 2 * Real.sqrt (cinv * N + R₂) + B)) ≤ N0star := by
  have h1 : N - R₁ ≤ trGh := by
    have := (abs_le.mp htr).1
    linarith
  have h2 : Real.sqrt frGh ≤ Real.sqrt (cinv * N + R₂) := Real.sqrt_le_sqrt hfr
  nlinarith [h0, h1, h2, hB, mul_le_mul_of_nonneg_left h2 hB]

/-- link to the Theorem-D constant: 2 − 1/cStar λ = HD λ by definition. -/
theorem two_sub_inv_cStar (lam : ℝ) : 2 - 1 / cStar lam = HD lam := rfl

/-! ### The D-interface for the traces (produced by Traces.lean, consumed by Endgame.lean)

Mirrors Zeta23.TracesBounds (PrimeSideTemp.lean) with the window moments (a, b, J) as data and the
ratio constant cRatio(λ₁; a, b, J) in place of F(λ₁).  tr1 is [eq:tr1] verbatim (prop:trace is
window-general); ratio/frhat carry the [eq:ratio-general] main terms. -/
structure TracesBoundsD (P : Params) (aT bT JT trG trG2 Ncnt : ℝ → ℝ) : Prop where
  /-- [eq:tr1] first equality (window-general prop:trace): tr G~ = a L N + O(L√X). -/
  tr1 : EvBound (fun T => trG T - aT T * P.L T * Ncnt T) (fun T => P.L T * Real.sqrt (P.X T))
  /-- [eq:ratio-general]: (tr G~)²/tr G~² = cRatio(λ₁; a, b, J) N (1 + O(E_T)). -/
  ratio : EvBound
    (fun T => trG T ^ 2 / trG2 T - cRatio (P.lam1 T) (aT T) (bT T) (JT T) * Ncnt T)
    (fun T => P.calE T * (cRatio (P.lam1 T) (aT T) (bT T) (JT T) * Ncnt T))
  /-- hat-units form consumed by the Thm-A-line endgame: the positive part of
  tr G~²/(aL)² − (1/cRatio)·N is O(E_T · (1/cRatio) N).  (Recorded separately since the
  division by (aL)² and the inversion are where TracesD does real work.) -/
  frhat : EvBound
    (fun T => max (trG2 T / (aT T * P.L T) ^ 2
        - (cRatio (P.lam1 T) (aT T) (bT T) (JT T))⁻¹ * Ncnt T) 0)
    (fun T => P.calE T * ((cRatio (P.lam1 T) (aT T) (bT T) (JT T))⁻¹ * Ncnt T))

/-! The ε-form wrappers live in Zeta23/ThmD/Endgame.lean (abstract) and Zeta23/ThmD/Final.lean (ζ). -/

end ThmD
end Zeta23
