/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ThmDE/TracesHyp.lean — [thm:E], last sentence: "Theorem D holds likewise."
The D-trace interface for a Dirichlet character: Zeta23.ThmD.TracesBoundsD
(Zeta23/ThmD/AssemblyD.lean) with λ₁ ↦ λ_{1,χ} = L/ℓ_{1,χ} (Zeta23.ThmE.lam1q).  Produced by
Zeta23/ThmDE/Traces.lean (FactsDChi ⇒ this), consumed by Zeta23/ThmDE/Endgame.lean.
-/
import Zeta23.ThmD.AssemblyD
import Zeta23.ThmE.TracesHypChi

noncomputable section

open Real

namespace Zeta23
namespace ThmDE

open ThmD ThmE

/-- **[eq:ratio-general] for L(s,χ)** with the Montgomery–Taylor window moments (a, b, J) as data:
tr1 = [eq:tr1] (window-general prop:trace); ratio/frhat carry the main term
cRatio(λ_{1,χ}; a, b, J)·N and its hat-units inverse.  Constants may depend on q. -/
structure TracesBoundsDChi (P : Params) (q : ℕ) (aT bT JT trG trG2 Ncnt : ℝ → ℝ) : Prop where
  tr1 : EvBound (fun T => trG T - aT T * P.L T * Ncnt T) (fun T => P.L T * Real.sqrt (P.X T))
  ratio : EvBound
    (fun T => trG T ^ 2 / trG2 T - cRatio (lam1q P q T) (aT T) (bT T) (JT T) * Ncnt T)
    (fun T => P.calE T * (cRatio (lam1q P q T) (aT T) (bT T) (JT T) * Ncnt T))
  frhat : EvBound
    (fun T => max (trG2 T / (aT T * P.L T) ^ 2
        - (cRatio (lam1q P q T) (aT T) (bT T) (JT T))⁻¹ * Ncnt T) 0)
    (fun T => P.calE T * ((cRatio (lam1q P q T) (aT T) (bT T) (JT T))⁻¹ * Ncnt T))

end ThmDE
end Zeta23

end
