/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
  Part of the Zeta23 formalization of the paper
  "More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
  Bracketed labels ([prop:cross], [eq:Msplit], …) and section numbers (§5.4, …) refer to that paper.
-/
import Zeta23.PrimeSideTemp

/-!
# [thm:traces] conclusions with an ABSTRACT error rate

LIGHT file (imports only Zeta23.PrimeSideTemp) so that Zeta23/Assembly.lean can import it:
`TracesBoundsE P Err aT trG trG2 Ncnt` = the four conclusions of the paper [thm:traces] ([eq:tr1] both forms,
[eq:tr2] second form, [eq:ratio]) with an arbitrary rate `Err : ℝ → ℝ` in place of the paper's 𝓔_T;
`TracesBounds` (Zeta23/PrimeSideTemp.lean) is the instance `Err := P.calE`, supplied by the paper's route
(Zeta23/PrimeSideB/Traces.lean via `TracesBounds.toE`).
-/

noncomputable section

open Filter Topology Real

namespace Zeta23

/-! ## [thm:traces] conclusions with an abstract rate -/

/-- The four conclusions of [thm:traces] with an abstract error rate `Err` (cf. `TracesBounds`,
Zeta23/PrimeSideTemp.lean, which is the case `Err = P.calE` = the paper's 𝓔_T). -/
structure TracesBoundsE (P : Params) (Err aT trG trG2 Ncnt : ℝ → ℝ) : Prop where
  tr1 : EvBound (fun T => trG T - aT T * P.L T * Ncnt T) (fun T => P.L T * Real.sqrt (P.X T))
  tr1' : EvBound (fun T => trG T - P.L T * Ncnt T) (fun T => Err T * (P.L T * Ncnt T))
  tr2 : EvBound (fun T => trG2 T - P.mainTr2 T) (fun T => Err T * P.mainTr2 T)
  ratio : EvBound (fun T => trG T ^ 2 / trG2 T - Ffun (P.lam1 T) * Ncnt T)
    (fun T => Err T * (Ffun (P.lam1 T) * Ncnt T))

lemma TracesBounds.toE {P : Params} {aT trG trG2 Ncnt : ℝ → ℝ}
    (h : TracesBounds P aT trG trG2 Ncnt) : TracesBoundsE P P.calE aT trG trG2 Ncnt :=
  ⟨h.tr1, h.tr1', h.tr2, h.ratio⟩

lemma TracesBoundsE.toTracesBounds {P : Params} {aT trG trG2 Ncnt : ℝ → ℝ}
    (h : TracesBoundsE P P.calE aT trG trG2 Ncnt) : TracesBounds P aT trG trG2 Ncnt :=
  ⟨h.tr1, h.tr1', h.tr2, h.ratio⟩

/-- [thm:traces] for the concrete prime-side data and the count of `Z`, abstract rate. -/
def ThmTracesHypE (P : Params) (Err : ℝ → ℝ) (Z : ZeroConfig) : Prop :=
  TracesBoundsE P Err P.a P.trGtilde P.trGtildeSq (fun T => (Z.N T (2 * T) : ℝ))

lemma thmTracesHyp_iff_E (P : Params) (Z : ZeroConfig) :
    ThmTracesHyp P Z ↔ ThmTracesHypE P P.calE Z :=
  ⟨fun h => TracesBounds.toE h, fun h => h.toTracesBounds⟩


end Zeta23

end
