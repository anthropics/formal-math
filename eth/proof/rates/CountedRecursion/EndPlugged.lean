/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.EndBounds
import Mathlib.Tactic

/-! # Theorem A (b) with the pieces computed by their algorithm

`recursionPluggedFrom : RecursionPluggedFrom`. The run of `RecursionCountedUpTo` has the price 1 for
a query to the tables. Raise it to 3 = 1 + 2 (`PricesScale`: no price grows more than three times,
so the cost is at most three times as large); then the queries to the pieces are answered by running
the algorithm and a query to the tables is passed on (`PiecesCounted.OracleFromAlgorithm`). The
states grow by the room of the algorithm at Λ and by the size of a query to the tables with its
answer, which is within the bound on the sizes (`tableQuery_le`); hence the constant C₀ + 1. -/

public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

/-- **Theorem A (b) with the pieces computed by their algorithm**, from the form with the priced
oracle. -/
theorem recursionPluggedFrom : RecursionPluggedFrom := by
  intro hU hP hO c
  obtain ⟨C₀, h⟩ := hU c
  refine ⟨C₀ + 1, fun ρ x₀ D Alg hA hS l lam B W hlam hB hW => ?_⟩
  obtain ⟨T, S, run, hT, hS'⟩ := h ρ x₀ D hS l lam B W hlam hB hW
  -- the price of a query to the tables is raised from 1 to 3
  have run3 : (recursion c x₀).Within (Sum.elim (answersOf (Levels.Gen.K x₀ l) lam W) fun g => if g.1.length ≤ lamMax ρ c x₀ l lam B then D.oracle g else none)
      (Sum.elim (fun _ => 1 + 2) (PiecesCounted.price c)) (top l lam B) (3 * T) S (.inl (clique (Levels.Gen.K x₀ l) lam fun w => W w.val).value) := by
    refine hP _ _ _ _ _ _ (upPrices c 1) _ _ T S 3 _ (by norm_num) (fun x => ?_) run
    cases x with
    | inl q => exact le_rfl
    | inr g => exact Nat.le_mul_of_pos_left _ (by norm_num)
  -- the queries to the pieces are answered by the algorithm
  have fin := hO TableQuery Ctx Ans (recursion c x₀) Alg D c hA.computes (answersOf (Levels.Gen.K x₀ l) lam W) (fun _ => 1) (top l lam B) (3 * T) S (lamMax ρ c x₀ l lam B)
    (Levels.Gen.K x₀ l + 2 * Levels.Gen.K x₀ l * lam + B + 3) _ (fun x v hx => size_tableQuery hW hx) run3
  refine ⟨_, _, fin, ?_, ?_⟩
  · have := timeBound_mono ρ hS.x₀_ge l hlam hB (Nat.le_succ C₀)
    push_cast
    linarith
  · have h1 := sizeBound_mono hS.x₀_ge l hlam hB (Nat.le_succ C₀)
    have h2 := tableQuery_le hS.x₀_ge l hlam hB (Nat.le_add_left 1 C₀)
    have e : ((S + PiecesCounted.room c (lamMax ρ c x₀ l lam B) + (Levels.Gen.K x₀ l + 2 * Levels.Gen.K x₀ l * lam + B + 3) + 4 : ℕ) : ℝ) =
        S + PiecesCounted.room c (lamMax ρ c x₀ l lam B) + ((Levels.Gen.K x₀ l + 2 * Levels.Gen.K x₀ l * lam + B + 3 + 4 : ℕ) : ℝ) := by
      push_cast
      ring
    rw [e]
    linarith

end ExplicitCost
