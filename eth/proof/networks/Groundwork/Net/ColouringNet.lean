/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Groundwork.Net.Defs
public import Groundwork.Net.Colouring

/-! The capacity between two classes of a network merged along a colouring is the sum of the
capacities between their members. -/

namespace Groundwork.Network

open Finset

variable {J J' σ τ : Type*}

/-- The capacity between two classes of the merged network, as an iterated sum. -/
public theorem merge_c [Fintype J] [LinearOrder J] [LinearOrder J'] (N : Network J σ τ) (χ : J → J') (s₀ : σ)
    (t₀ : τ) (G G' : J') :
    (N.merge χ s₀ t₀).c G G' = ∑ a with χ a = G, ∑ b with χ b = G', N.c a b := by
  change ∑ p : J × J with χ p.1 = G ∧ χ p.2 = G', N.c p.1 p.2 = _
  rw [sum_filter, Fintype.sum_prod_type, sum_filter]
  refine sum_congr rfl fun a _ => ?_
  by_cases ha : χ a = G
  · rw [if_pos ha, sum_filter]
    exact sum_congr rfl fun b _ => by simp [ha]
  · simp [ha]

end Groundwork.Network
