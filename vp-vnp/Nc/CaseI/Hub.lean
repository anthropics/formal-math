/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.CaseI.Lower

/-!
# Two hubs for a balanced set

The end of the pair {a, b}, a < b, at a stands at e_a / 2 and the end at b at -e_a / 2. For a balanced set A there is a
point x of norm 2 / (9 √k) such that the sum of the distances from the ends in A to x and from the other ends to -x is at
most k (k - 1) / 2 - 4 k / 81.
-/

namespace Nc.CaseI

open Finset

variable {k : ℕ}

/-- The position of an end. -/
noncomputable def endPos (e : Pr k) (i : Fin 2) : EuclideanSpace ℝ (Fin k) :=
  (if decide (i = 0) then (1 / 2 : ℝ) else -(1 / 2)) • EuclideanSpace.single e.1.1 1

theorem endPos_zero (e : Pr k) : endPos e 0 = (1 / 2 : ℝ) • EuclideanSpace.single e.1.1 1 := by simp [endPos]

theorem endPos_one (e : Pr k) : endPos e 1 = (1 / 2 : ℝ) • -EuclideanSpace.single e.1.1 1 := by
  simp [endPos, smul_neg, neg_smul]

theorem dist_endPos (e : Pr k) : dist (endPos e 0) (endPos e 1) = 1 := by
  rw [endPos_zero, endPos_one, dist_eq_norm, smul_neg, sub_neg_eq_add, ← add_smul]
  norm_num

/-- The pair is separated by A. -/
def Sep (A : Finset (Fin k)) (e : Pr k) : Prop := ¬ (e.1.1 ∈ A ↔ e.1.2 ∈ A)

instance (A : Finset (Fin k)) (e : Pr k) : Decidable (Sep A e) := by unfold Sep; infer_instance

/-- The direction of the hubs: at a, the number of pairs {a, b}, a < b, that A separates, with the sign of a. -/
noncomputable def hubDir (A : Finset (Fin k)) : EuclideanSpace ℝ (Fin k) :=
  ∑ e : Pr k with Sep A e, (if e.1.1 ∈ A then (1 : ℝ) else -1) • EuclideanSpace.single e.1.1 1

/-- The sign of a node. -/
noncomputable def sideSign (A : Finset (Fin k)) (a : Fin k) : ℝ := if a ∈ A then 1 else -1

/-- The number of pairs that a set separates. -/
theorem sum_sep (A : Finset (Fin k)) :
    ∑ e : Pr k, (if Sep A e then (1 : ℝ) else 0) = A.card * ((k : ℝ) - A.card) := by
  have h1 := sum_pairs (k := k) fun a b => if a ∈ A ∧ b ∉ A then (1 : ℝ) else 0
  have h2 : ∀ e : Pr k, (if Sep A e then (1 : ℝ) else 0) = (if e.1.1 ∈ A ∧ e.1.2 ∉ A then (1 : ℝ) else 0) +
      (if e.1.2 ∈ A ∧ e.1.1 ∉ A then (1 : ℝ) else 0) := by
    intro e
    by_cases ha : e.1.1 ∈ A <;> by_cases hb : e.1.2 ∈ A <;> simp [Sep, ha, hb]
  rw [Finset.sum_congr rfl fun e _ => h2 e, h1]
  have h3 : ∀ a b : Fin k, (if a = b then (0 : ℝ) else if a ∈ A ∧ b ∉ A then 1 else 0) =
      if a ∈ A then (if b ∈ A then 0 else 1) else 0 := by
    intro a b
    by_cases hab : a = b
    · subst hab; by_cases ha : a ∈ A <;> simp [ha]
    · by_cases ha : a ∈ A <;> by_cases hb : b ∈ A <;> simp [hab, ha, hb]
  simp only [h3]
  have h4 : ∀ a : Fin k, (∑ b : Fin k, if a ∈ A then (if b ∈ A then (0 : ℝ) else 1) else 0) =
      if a ∈ A then (k : ℝ) - A.card else 0 := by
    intro a
    by_cases ha : a ∈ A
    · simp only [if_pos ha]
      rw [sum_ite_card]
      ring
    · simp [if_neg ha]
  simp only [h4]
  rw [sum_ite_card]
  ring

theorem inner_hubDir (A : Finset (Fin k)) (w : EuclideanSpace ℝ (Fin k)) :
    inner ℝ (hubDir A) w = ∑ e : Pr k, if Sep A e then sideSign A e.1.1 * w e.1.1 else 0 := by
  rw [hubDir, sum_inner, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h : Sep A e
  · rw [if_pos h, if_pos h, real_inner_smul_left, EuclideanSpace.inner_single_left]
    simp [sideSign]
  · rw [if_neg h, if_neg h]

end Nc.CaseI
