/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import FixedWidthSteps.RouteDefs

/-! # «Its hypothesis holds by (a) and (b)»

The levels of the recursion are the premise `PairsToBound.TheRecursionHasLevels`. What is added here
is the clause on the number of the proviso: by the last clause of `ChainOfInequalities`, a number
between 0.85ρ^ℓ and ρ^ℓ lies in [e_ℓ, 2e_ℓ]. -/

public section

namespace FixedWidthSteps

open PairsToBound FixedWidth

/-- That the hypothesis holds, from the levels of the recursion and the chain of inequalities. -/
theorem hypothesisHoldsFrom : HypothesisHoldsFrom := by
  intro hL hC c
  obtain ⟨C₀, h⟩ := hL c
  refine ⟨C₀, fun ρ x₀ P A val hP hx hc => ?_⟩
  obtain ⟨Q, hpoly, hK, hpick⟩ := h ρ x₀ P A val hP hx hc
  refine ⟨Q, hpoly, hK, hpick, fun num hnum hb => ⟨hnum, fun l => ?_⟩⟩
  rw [hK l]
  exact (hC ρ x₀ l hP.rho_ge hP.rho_lt hx).2.2.2 _ (hb l).1 (hb l).2

end FixedWidthSteps
