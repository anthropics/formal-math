/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsificationLemma.Cal.Defs
import SparsificationLemma.Cal.Beta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-! # Calabro's thresholds satisfy the conditions `ThrC` with τ = α

This file proves `StThrCal`. Positivity, β₁ = 2 and α·β_r ≤ θ_r are read off the definitions and the
closed form of β_c. The condition at a size i ≥ 2 is
4·θ(i−1) + Σ_{i' < i} 2·θ(i−i')·β(i') ≤ β(i). Put S = Σ_{h=1}^{i−1} 2α·β(i−h)·β(h), so that β(i) =
2·S by the recursion. The term i' = 0 of the sum vanishes, as β₀ = 0, and the rest of the sum is S.
And
4·θ(i−1) = 2α·β(i−1)·β(1) is the term h = 1 of S, so the left side is at most 2·S = β(i). -/

public section

namespace SparsificationLemma.Cal

open Finset

/-- Calabro's thresholds satisfy the four conditions with τ = α, for every k and every α ≥ 1. -/
theorem stThrCal : StThrCal := by
  intro α k hα
  refine ⟨fun i => ?_, (betaC_one α).ge, fun i hi _ => ?_, fun r => ?_⟩
  · rcases i with _ | i
    · exact Nat.succ_pos 1
    · exact Nat.mul_pos hα (betaC_pos hα i)
  · have hS : ∑ i' ∈ range i, 2 * thetaC α (i - i') * betaC α i' = ∑ h ∈ Ico 1 i, 2 * α * betaC α (i - h) * betaC α h := by
      rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega), betaC_zero, Nat.mul_zero, Nat.zero_add]
      refine sum_congr rfl fun h hh => ?_
      obtain ⟨h1, h2⟩ := mem_Ico.1 hh
      rw [thetaC_of_pos α (by omega : 1 ≤ i - h), Nat.mul_assoc 2 α]
    have h1 : 4 * thetaC α (i - 1) ≤ ∑ h ∈ Ico 1 i, 2 * α * betaC α (i - h) * betaC α h := by
      have e : 4 * thetaC α (i - 1) = 2 * α * betaC α (i - 1) * betaC α 1 := by
        rw [thetaC_of_pos α (by omega : 1 ≤ i - 1), betaC_one]; ring
      rw [e]
      exact single_le_sum (f := fun h => 2 * α * betaC α (i - h) * betaC α h) (fun _ _ => Nat.zero_le _) (mem_Ico.2 ⟨le_refl 1, by omega⟩)
    have h2 : betaC α i = 2 * ∑ h ∈ Ico 1 i, 2 * α * betaC α (i - h) * betaC α h := by
      rw [stBetaRec α i hi, mul_sum]
      exact sum_congr rfl fun h _ => by ring
    rw [hS, h2]
    omega
  · rcases r with _ | r
    · rw [betaC_zero, Nat.mul_zero]; exact Nat.zero_le _
    · exact le_refl _

end SparsificationLemma.Cal
