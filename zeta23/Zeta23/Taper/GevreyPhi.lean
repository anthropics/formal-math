/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Taper/GevreyPhi.lean — the L¹ bounds on the iterated derivatives of
the concrete taper φ(u) = ϱ((L/2−|u|)/w) that the Gevrey tail lemma consumes.
-/
import Zeta23.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

noncomputable section

namespace Zeta23

/-- The Gevrey taper bound, as a hypothesis on (P, T): φ = P.phi T (as a ℂ-valued function)
is C^∞ and ‖φ^{(k)}‖_{L¹} ≤ 2B·w·(A/w)^k·k^{sk} for all k ≥ 1  (= 2B w^{1−k} A^k k^{sk}). -/
structure Params.GevreyPhiBound (P : Params) (T : ℝ) (s A B : ℝ) : Prop where
  one_lt : 1 < s
  A_pos : 0 < A
  B_pos : 0 < B
  smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : ℝ => (P.phi T u : ℂ))
  bound : ∀ k : ℕ, 1 ≤ k →
    ∫ u, ‖iteratedDeriv k (fun u : ℝ => (P.phi T u : ℂ)) u‖ ≤ 2 * B * P.w * (A / P.w) ^ k * (k : ℝ) ^ (s * k)

end Zeta23
