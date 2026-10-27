/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import PaddedDescent.F.Interfaces
import Mathlib.Tactic.Convert
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Marks and layers: the values of the networks of the admissible profiles add up to the cut-off sum

A layer is one of the sets of clauses in the list Ls, and `layP Ls P i` is the set of the members of
P in layer i. The layers, and the cut-off at w members in every layer, are a variant of the cut-off
of Appendix D that the paper does not state.
The value of the network of a profile y counts, with signs, the pairs (σ, P) with the profile y
(StMarkVal). Every P has exactly one profile, and that profile is admissible exactly if P has at
most w members in every layer (StProfSum).
So the sum over the admissible profiles counts, with signs, the pairs (σ, P) in which P has at most
w members in every layer, and for a fixed σ that signed number is the product of the cut-off sums
(StPiSum). -/

namespace PaddedDescent.F.Mark.Sum

open Groundwork Groundwork.Prog Finset PaddedDescent.F PaddedDescent.F.Mark

/-- The central identity, from the value of one network, the sum over the profiles and the sum over
the sets of violated clauses. -/
public theorem stMarkSum (hV : StMarkVal) (hP : StProfSum) (hS : StPiSum) : StMarkSum := by
  classical
  intro k gu nu βu bu w Ls hg h0 hb hw
  have h1 : ∀ y ∈ Finset.range (nProf gu.length (cls Ls).length Ls.length),
      (if adm k gu.length nu.length w Ls y = true then (markN gu.length ((gu, nu, βu, bu), (Ls, y))).value else 0) =
        ∑ σ : Fin nu.length → Bool, ∑ P ∈ (vset (Mark.ext σ) Ls).powerset,
          sgnP Ls P * (if adm k gu.length nu.length w Ls y = true ∧ Match gu.length nu.length Ls y P then (1 : ℤ) else 0) := by
    intro y _
    rw [hV k gu nu βu bu Ls y hg h0 hb hw]
    by_cases h : adm k gu.length nu.length w Ls y = true
    · rw [if_pos h]
      refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun P _ => ?_
      by_cases hm : Match gu.length nu.length Ls y P
      · simp [h, hm]
      · simp [hm]
    · simp [h]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  unfold trunc
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_comm, ← hS w Ls (Mark.ext σ)]
  refine Finset.sum_congr rfl fun P hPm => ?_
  have hsub : P ⊆ Finset.range (cls Ls).length := (Finset.mem_powerset.1 hPm).trans (Finset.filter_subset _ _)
  have h2 := hP k gu.length nu.length w Ls P hg hw hsub
  rw [← Finset.mul_sum]
  by_cases hc : ∀ i < Ls.length, (layP Ls P i).card ≤ w
  · rw [if_pos hc] at h2
    rw [if_pos hc]
    have h3 : (∑ y ∈ Finset.range (nProf gu.length (cls Ls).length Ls.length),
        if adm k gu.length nu.length w Ls y = true ∧ Match gu.length nu.length Ls y P then (1 : ℤ) else 0) = 1 := by
      convert h2
    rw [h3, mul_one]
  · rw [if_neg hc] at h2
    rw [if_neg hc]
    have h3 : (∑ y ∈ Finset.range (nProf gu.length (cls Ls).length Ls.length),
        if adm k gu.length nu.length w Ls y = true ∧ Match gu.length nu.length Ls y P then (1 : ℤ) else 0) = 0 := by
      convert h2
    rw [h3, mul_zero]

end PaddedDescent.F.Mark.Sum
