/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CircuitLowerBound.Tab.Spec
import Mathlib.Tactic

/-! # The circuit lower bound for E^NP (Section 7): the statement `StTab`, that every machine has a table (one step of the machine written as a table), follows from the three statements `StPack`, `StSpec` and `StSpecTab` -/

public section

namespace CircuitLowerBound

open ENP Turing Tab

/-- Every machine has a table. -/
theorem stTab_of (h1 : StPack) (h2 : StSpec) (h3 : StSpecTab) : StTab := fun N hfin => by
  have : ∀ k, Finite (N.tm.Γ k) := hfin
  have : Finite (Case N) := inferInstance
  obtain ⟨e, hg, hl, he⟩ := h3 N hfin
  refine ⟨e, fun L P hF => ?_⟩
  rw [h1 e L P hg hF, he, bq, hl]
  exact h2 N (bt e L) P (by have := hF.1; unfold bt; omega) hF.2

end CircuitLowerBound
