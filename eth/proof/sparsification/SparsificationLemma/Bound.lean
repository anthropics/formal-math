/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsificationLemma.Defs
import all StepMachines.Math.Sparsify
import UniformInK.Spars.Bound
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! # The counts along a path, for thresholds with `ThrC`

This file proves `StThrOfU` (the conditions `ThrU` together with 2 ≤ β 1 imply the conditions
`ThrC`) and `StBoundC`: a path has at most (β 0 + … + β (k-1))·n steps, and its steps of the second
kind use at most
(k−1)·n units, τ each. It follows the argument of proof/sparsification/UniformInK/Spars/Bound.lean,
except in two places.
At size 1 the number of added clauses is bounded directly. By `InvU.acc` it is at most the number of
those that are still present, since no clause of size 0 is ever added, and there are only 2n clauses
of one literal.
In the count of the units, the size r = 0 contributes nothing: a step of the second kind that adds
clauses of size 0 would add θ 0 ≥ 1 of them, and none is ever added. -/

public section

namespace SparsificationLemma

open Finset Groundwork Groundwork.Sparsify WidthK UniformInK

/-- The conditions `ThrU` together with 2 ≤ β 1 imply the conditions `ThrC`: `ThrC.step` asks at the
sizes i ≥ 2 what `ThrU.step` asks at all sizes i ≥ 1. -/
theorem stThrOfU : StThrOfU := fun _ _ _ _ h1 h => ⟨h.pos, h1, fun i hi hik => h.step i (by omega) hik, h.mul⟩

namespace Bound

variable {α : Type*} [DecidableEq α] {θ β : ℕ → ℕ} {k τ n : ℕ} {φ F N : Finset (Finset α)} {U : Finset α} {a : ℕ → ℕ} {p t : ℕ}

/-- At most β i · n clauses of size i < k are added along a path. -/
theorem acc_le (hT : ThrC k τ θ β) (hU : U.card ≤ 2 * n) (hFU : ∀ C ∈ F, C ⊆ U) (h : InvU θ F N a) (ha0 : a 0 = 0) (i : ℕ) (hik : i < k) :
    a i ≤ β i * n := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    obtain rfl | rfl | hi : i = 0 ∨ i = 1 ∨ 2 ≤ i := by omega
    · rw [ha0]; exact Nat.zero_le _
    · have e := h.acc 1
      rw [sum_range_one, ha0, Nat.mul_zero, Nat.add_zero] at e
      have c : (lay N 1).card ≤ U.card := card_ones_le (F := N) fun C hC => hFU C (h.sub hC)
      calc a 1 ≤ (lay N 1).card := e
        _ ≤ 2 * n := c.trans hU
        _ ≤ β 1 * n := Nat.mul_le_mul_right _ hT.one
    have h2 : ∑ i' ∈ range i, 2 * θ (i - i') * a i' ≤ (∑ i' ∈ range i, 2 * θ (i - i') * β i') * n := by
      rw [sum_mul]
      refine sum_le_sum fun i' hi' => ?_
      have hlt := mem_range.1 hi'
      rw [Nat.mul_assoc (2 * θ (i - i'))]
      exact Nat.mul_le_mul_left _ (ih i' hlt (hlt.trans hik))
    calc a i ≤ (lay N i).card + ∑ i' ∈ range i, 2 * θ (i - i') * a i' := h.acc i
      _ ≤ 4 * θ (i - 1) * n + (∑ i' ∈ range i, 2 * θ (i - i') * β i') * n :=
        Nat.add_le_add (UniformInK.Bound.card_lay_le hU hFU h (by omega)) h2
      _ = (4 * θ (i - 1) + ∑ i' ∈ range i, 2 * θ (i - i') * β i') * n := by rw [Nat.add_mul]
      _ ≤ β i * n := Nat.mul_le_mul_right _ (hT.step i hi hik)

/-- A path has at most (β 0 + … + β (k-1)) · n steps, and its steps of the second kind use at most
(k−1) · n units, τ each. -/
theorem bound (hT : ThrC k τ θ β) (hU : U.card ≤ 2 * n) (hφ : ∀ C ∈ φ, C ⊆ U) (h : NodeU θ k τ φ F p t) :
    p ≤ (∑ i ∈ range k, β i) * n ∧ t ≤ (k - 1) * n := by
  have hFU := UniformInK.Bound.subset_of hφ h
  obtain ⟨-, N, a, hh, hI, ha0, hh1, hp, ht⟩ := h
  have ha := acc_le hT hU hFU hI ha0
  constructor
  · rw [sum_mul]
    exact hp.trans (sum_le_sum fun i hi => ha i (mem_range.1 hi))
  have hr : ∀ r < k, τ * hh r ≤ n := by
    intro r hr
    have har := ha r hr
    have h1 : τ * hh r * β r ≤ n * β r := by
      calc τ * hh r * β r = hh r * (τ * β r) := by ring
        _ ≤ hh r * θ r := Nat.mul_le_mul_left _ (hT.mul r)
        _ ≤ a r := hh1 r
        _ ≤ β r * n := har
        _ = n * β r := Nat.mul_comm _ _
    rcases Nat.eq_zero_or_pos (β r) with h0 | h0
    · have h2 := (hh1 r).trans har
      rw [h0, Nat.zero_mul] at h2
      have h3 : hh r = 0 := (Nat.mul_eq_zero.1 (Nat.le_zero.1 h2)).resolve_right (hT.pos r).ne'
      rw [h3, Nat.mul_zero]; exact Nat.zero_le _
    · exact Nat.le_of_mul_le_mul_right h1 h0
  have h0 : hh 0 = 0 := by
    have h2 := hh1 0
    rw [ha0] at h2
    exact (Nat.mul_eq_zero.1 (Nat.le_zero.1 h2)).resolve_right (hT.pos 0).ne'
  rcases k with _ | k
  · simpa using ht
  · refine ht.trans ?_
    rw [sum_range_succ', h0, Nat.add_zero, mul_sum]
    exact (sum_le_card_nsmul _ _ n fun r hr' => hr (r + 1) (by have := mem_range.1 hr'; omega)).trans (by simp)

end Bound

/-- `Bound.bound`, in the form of the statement. -/
theorem stBoundC : StBoundC := fun _ _ _ _ _ _ _ _ _ _ _ _ hT hU hφ h => Bound.bound hT hU hφ h

end SparsificationLemma
