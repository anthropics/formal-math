/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.EndBounds
public import CountedRecursion.Within
import Mathlib.Tactic

/-! # Theorem A (b) as `CliqueLevels.Solves` has it

* `recursionSolvesFrom : RecursionSolvesFrom`. The machine `cliqueMachine c x₀ Alg` is
  `recursionWith c x₀ Alg` with the input (ℓ, λ, B), with answers that are integers (`ReadAsRuns`)
  and with an integer as its result. Three times the bound for C₁, and twice the bound on the sizes
  for C₁ with the room of the algorithm (`RoomIsWithinTheBound`, constant C₂), are within the bound
  for C₁ + C₂ + 1. -/

public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

/-- **Theorem A (b)**, in the form of `CliqueLevels.Solves`, from the form with the algorithm of the
pieces. -/
theorem recursionSolvesFrom : RecursionSolvesFrom := by
  intro hP hRoom hRA hPoly c
  obtain ⟨C₁, h₁⟩ := hP c
  obtain ⟨C₂, h₂⟩ := hRoom c
  refine ⟨C₁ + C₂ + 1, fun ρ x₀ D Alg hA hS => ⟨(hPoly c x₀ Alg hA.polyTimeSteps).2, fun l lam B W hlam hB hW => ?_⟩⟩
  obtain ⟨T, S, ⟨own, L, hr, hle⟩, hT, hS'⟩ := h₁ ρ x₀ D Alg hA hS l lam B W hlam hB hW
  have hroom := h₂ ρ x₀ l lam B hS.is.rho_ge hS.is.rho_lt hS.is.c_pos hS.x₀_ge hS.x₀_c hlam hB
  -- the answers are integers
  have r1 : (readAs Sum.inl (recursionWith c x₀ Alg)).Within (tables (Levels.Gen.K x₀ l) lam W) QueryMachine.unitCost (top l lam B) T S (.inl (clique (Levels.Gen.K x₀ l) lam fun w => W w.val).value) :=
    ⟨own, L, hRA _ _ _ _ _ Sum.inl _ (answersOf (Levels.Gen.K x₀ l) lam W) (tables (Levels.Gen.K x₀ l) lam W) _ own S L _ (fun _ => rfl) hr, hle⟩
  -- the input is (ℓ, λ, B), the result an integer
  have r2 : (cliqueMachine c x₀ Alg).Within (tables (Levels.Gen.K x₀ l) lam W) QueryMachine.unitCost (unary l, unary lam, unary B) T S (clique (Levels.Gen.K x₀ l) lam fun w => W w.val).value :=
    mapOut_within (g := asInt) (mapIn_within (g := fun h : Head => ((h, none) : Ctx)) (a := (unary l, unary lam, unary B)) r1)
  have m1 := timeBound_mono ρ hS.x₀_ge l hlam hB (Nat.le_add_right C₁ C₂)
  have m2 := timeBound_mono ρ hS.x₀_ge l hlam hB (Nat.le_add_left C₂ C₁)
  have m3 := three_timeBound_le ρ hS.x₀_ge l hlam hB (C₁ + C₂)
  have m4 := sizeBound_le_timeBound hS.is.rho_ge hS.x₀_ge l hlam hB C₁
  refine ⟨T, S, r2, ?_, ?_⟩
  · change (T : ℝ) ≤ timeBound ρ x₀ (C₁ + C₂ + 1) l lam B
    linarith
  · change (S : ℝ) ≤ timeBound ρ x₀ (C₁ + C₂ + 1) l lam B
    linarith

end ExplicitCost
