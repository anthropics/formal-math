/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Net.Defs
import Mathlib.Tactic.Convert
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Step 3, «Profiles»: the values of the networks of the admissible profiles add up to the right side of display (65)

The value of the network of a profile y is the sum of the terms of the pairs (ξ, P) that belong to y
(StVal). For g > 0, well-formed data and a set P of places of objects, exactly one admissible
profile has P if P is within
the limits |Π₀| = n̄ + 1 (for F: ≤ n̄) and |Π₁| + … + |Π_r| ≤ M, and none otherwise (StProf). So the
sum over the admissible profiles is the sum of the terms of the pairs (ξ, P) with P within the
limits, which is the right side of
display (65) (StTuples). The same argument as in proof/rates/PaddedDescent/F/MarkSum.lean. -/

namespace VariableBound.Net.Total

open Groundwork Groundwork.Prog Finset PaddedDescent.F

/-- Step 3, «Profiles»: «each right side of (65) is the sum of the values of the networks of the
admissible profiles», for g > 0 nodes and well-formed data (the formula Φ and the list 𝚲 of checks).
Conditional: the statements StVal (the value of one
network), StProf (the sum over the profiles) and StTuples (the sum over the sets of objects) are
hypotheses here; `VariableBound.Net.Main.total` supplies them. -/
public theorem stTotal (hV : StVal) (hP : StProf) (hT : StTuples) : StTotal := by
  classical
  intro k g n nb M D fl hg hW
  have h1 : ∀ y ∈ Finset.range (nPr g D),
      (if admD k g n nb M D fl y = true then (netDN g (ctx g n D y fl)).value else 0) =
        ∑ σ : Fin n → Bool, ∑ P ∈ (vset (Mark.ext σ) D).powerset,
          wt D fl P * (if admD k g n nb M D fl y = true ∧ Match g n D y P then (1 : ℤ) else 0) := by
    intro y _
    rw [hV k g n D y fl hg hW]
    by_cases h : admD k g n nb M D fl y = true
    · rw [if_pos h]
      refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun P _ => ?_
      by_cases hm : Match g n D y P
      · simp [h, hm]
      · simp [hm]
    · simp [h]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, ← hT k n nb M D fl hW]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun P hPm => ?_
  have hsub : P ⊆ Finset.range (objs D).length := (Finset.mem_powerset.1 hPm).trans (Finset.filter_subset _ _)
  have h2 := hP k g n nb M D fl P hg hW hsub
  rw [← Finset.mul_sum]
  by_cases hc : Lim nb M D fl P
  · rw [if_pos hc] at h2
    rw [if_pos hc]
    have h3 : (∑ y ∈ Finset.range (nPr g D), if admD k g n nb M D fl y = true ∧ Match g n D y P then (1 : ℤ) else 0) = 1 := by
      convert h2
    rw [h3, mul_one]
  · rw [if_neg hc] at h2
    rw [if_neg hc]
    have h3 : (∑ y ∈ Finset.range (nPr g D), if admD k g n nb M D fl y = true ∧ Match g n D y P then (1 : ℤ) else 0) = 0 := by
      convert h2
    rw [h3, mul_zero]

end VariableBound.Net.Total
