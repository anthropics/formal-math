/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.CountBase
public import CountedRecursion.CountStep
public import Tower.Cost
import Mathlib.Tactic

/-! # The count, by induction on the depth

The cost of the tower at the depth j, if a query to the tables of the instance costs t ≥ 1, is at
most t times the bound of the theorem for the depth j (at the bounds for λ and B). The base is
`CountBase`. For the step, the recursion for the cost of the tower is written out
(`Tower.CostShape`);
a call costs at most (cost of an entry + 2) times the bound of the depth below, by the induction
hypothesis, and 2 more; `CountStep` bounds the sum, and `ExponentFits` the exponent of Ξ, with C₀ =
2(c + C₄ + 1). The paper has C₀ = 2(c + C₄ + 1) + C₅. Here C₅ is not needed for the count: a term of
brute force costs K₀ + 1 steps and K₀ queries, so `CountBase` holds for every C₀ ≥ 1; the C₅ of
`SolverBase` bounds the sizes of the states, and goes into the constant of `RecursionMeets`. -/

public section

namespace ExplicitCost

open Levels.Gen Printed QueryMachines

/-- `TotalCountFrom`: the cost bound of Theorem A(b) for the tower, by induction on the depth, from
the base (`CountBase`), the step (`CountStep`), the bound on the exponent of Ξ (`ExponentFits`) and
the shape of the cost recursion (`Tower.CostShape`), with C₀ = 2(c + C₄ + 1). -/
theorem totalCountFrom : TotalCountFrom := by
  intro hB hS hF hShape c C
  obtain ⟨C₄, hC₄⟩ := hS c C
  refine ⟨2 * (c + C₄ + 1), fun ρ x₀ l lam B h1 h2 h3 h4 h5 h6 h7 => ?_⟩
  have hN : Numbers ρ c x₀ lam B := ⟨h1, h2, h3, h4, h5, h6, h7⟩
  have key : ∀ j, j ≤ l → ∀ t, 1 ≤ t →
      (Tower.cost (solverCost C ρ c x₀ l lam B) (entryCost C ρ c x₀ l lam B) j t : ℝ) ≤ t * levelBound ρ c x₀ (2 * (c + C₄ + 1)) l lam B j := by
    intro j
    induction j with
    | zero =>
      intro _ t ht
      exact hB C ρ c x₀ _ l lam B t hN (by omega) ht
    | succ j ih =>
      intro hj t ht
      have eq1 : Tower.cost (solverCost C ρ c x₀ l lam B) (entryCost C ρ c x₀ l lam B) (j + 1) t =
          solverOwn C ρ c x₀ l lam B (j + 1) + solverCalls ρ c x₀ l lam B (j + 1) *
            (Tower.cost (solverCost C ρ c x₀ l lam B) (entryCost C ρ c x₀ l lam B) j (entryCost C ρ c x₀ l lam B j t + 2) + 2) + 0 * t :=
        hShape (solverOwn C ρ c x₀ l lam B) (solverCalls ρ c x₀ l lam B) (solverAsks ρ c x₀ l lam B) (entryOwn C ρ c x₀ l lam B) (entryAsks C ρ c x₀ l lam B) j t
      have ih' := ih (by omega) (entryCost C ρ c x₀ l lam B j t + 2) (by omega)
      have hs := hC₄ ρ x₀ (2 * (c + C₄ + 1)) l lam B j t hN (by omega) ht
      have hx1 : 1 ≤ x₀ := by omega
      have hXn := four_mul_le_xiAt hx1 ρ c l lam B j (one_le_bitsAt hN hj)
      have hX1 : (1 : ℝ) ≤ (xiAt ρ c x₀ l lam B j : ℝ) := by exact_mod_cast (by omega : 1 ≤ xiAt ρ c x₀ l lam B j)
      have hf := hF c C₄ (2 * (c + C₄ + 1)) x₀ j h4 h5 le_rfl
      rw [eq1]
      push_cast at ih' ⊢
      have a1 : (solverCalls ρ c x₀ l lam B (j + 1) : ℝ) * ((Tower.cost (solverCost C ρ c x₀ l lam B) (entryCost C ρ c x₀ l lam B) j (entryCost C ρ c x₀ l lam B j t + 2) : ℝ) + 2) ≤
          (solverCalls ρ c x₀ l lam B (j + 1) : ℝ) * (((entryCost C ρ c x₀ l lam B j t : ℝ) + 2) * levelBound ρ c x₀ (2 * (c + C₄ + 1)) l lam B j + 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
      have a2 : (t : ℝ) * ((2 : ℝ) ^ (e ρ x₀ (j + 1) * (K x₀ (j + 1) : ℝ) ^ 2 * lamAt ρ c x₀ l lam B (j + 1)) *
          (xiAt ρ c x₀ l lam B j : ℝ) ^ (c * g x₀ j ^ 4 / 2 + g x₀ j + K x₀ j ^ 2 + C₄ + (c + 5) * (2 * (c + C₄ + 1)) * K x₀ j ^ 2)) ≤ t * levelBound ρ c x₀ (2 * (c + C₄ + 1)) l lam B (j + 1) := by
        rw [levelBound_succ]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX1 hf) (by positivity)) (Nat.cast_nonneg _)
      linarith
  have h := key l le_rfl 1 le_rfl
  unfold levelBound at h
  rw [lamAt_self, bitsAt_self] at h
  simpa using h

/-- `TotalCount`: `totalCountFrom` applied to `countBase`, `countStep`, `exponentFits` and
`Tower.costShape`. -/
theorem totalCount : TotalCount := totalCountFrom countBase countStep exponentFits Tower.costShape

end ExplicitCost
