/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.EndBounds
public import CountedRecursion.CliqueReads
import Mathlib.Tactic

/-! # Theorem A (b) with the pieces as a priced oracle that is asked only about strings of at most Λ bits, from the steps

* `top_inBounds`, `top_fits`: the outermost instance (ℓ, λ, B) with its tables is a well-formed
  instance of the specification, within its own bounds.
* `recursionCountedUpToFrom : RecursionCountedUpToFrom`: the solver and the procedure meet the
  specification (`RecursionMeets`), so the tower returns the value at the cost of the recursion
  (`QueryMachines.Tower.TowerRuns`), which is within the bound of the theorem (`TotalCount`), on
  states within the bound on the sizes (`TotalRoom`). The value of the clique reads the tables only
  on settings (`clique_readTables`). -/

public section

namespace ExplicitCost

open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

/-- The level of the outermost instance. -/
theorem cLev_top (l lam B : ℕ) : cLev (top l lam B) = l := length_unary l

/-- Its label length. -/
theorem cLam_top (l lam B : ℕ) : cLam (top l lam B) = lam := length_unary lam

/-- Its bound on the bits of the tables. -/
theorem cB_top (l lam B : ℕ) : cB (top l lam B) = B := length_unary B

/-- The outermost instance is within the bounds that hold along the recursion from it. -/
theorem top_inBounds (ρ : ℝ) (c x₀ l lam B : ℕ) : InBounds ρ c x₀ l lam B (top l lam B) := by
  unfold InBounds lamAt bitsAt
  rw [cLev_top, cLam_top, cB_top, Nat.sub_self]
  exact ⟨le_rfl, le_rfl, le_rfl⟩

/-- The outermost instance with its tables is «the (K_ℓ, λ)-clique with |W_w| < 2^B». -/
theorem top_fits (x₀ l : ℕ) {lam B : ℕ} (hlam : 1 ≤ lam) (hB : 1 ≤ B) {W : ℕ → List Bool → ℤ} (hW : ∀ w < Levels.Gen.K x₀ l, ∀ z ∈ words ((Levels.Gen.K x₀ l - 1) * lam), |W w z| < 2 ^ B) :
    Fits x₀ (top l lam B) (answersOf (Levels.Gen.K x₀ l) lam W) := by
  unfold Fits
  rw [cLev_top, cLam_top, cB_top]
  exact ⟨hlam, hB, W, hW, rfl⟩

/-- **How the steps give the theorem**, with the pieces asked only about strings of at most Λ bits. -/
theorem recursionCountedUpToFrom : RecursionCountedUpToFrom := by
  intro hM hT hR hTR c
  obtain ⟨C, hC⟩ := hM c
  obtain ⟨C₁, hC₁⟩ := hT c C
  obtain ⟨C₂, hC₂⟩ := hR c C
  refine ⟨max C₁ C₂, fun ρ x₀ D hS l lam B W hlam hB hW => ?_⟩
  have run : (recursion c x₀).Within (Sum.elim (answersOf (Levels.Gen.K x₀ l) lam W) (piecesUpTo D (lamMax ρ c x₀ l lam B))) (upPrices c 1) (top l lam B)
      (Tower.cost (solverCost C ρ c x₀ l lam B) (entryCost C ρ c x₀ l lam B) (cLev (top l lam B)) 1)
      (Tower.towerSize (cLev (top l lam B)) (roomAll C ρ c x₀ l lam B) (roomAll C ρ c x₀ l lam B) (roomAll C ρ c x₀ l lam B))
      (.inl (clique (Levels.Gen.K x₀ (cLev (top l lam B))) (cLam (top l lam B)) fun w => readTables (answersOf (Levels.Gen.K x₀ l) lam W) w.val).value) :=
    hTR Ctx TableQuery PieceQuery Ans (spec D c x₀ (InBounds ρ c x₀ l lam B)) _ _ _ _ _ _ _ _ _ (hC ρ x₀ D hS l lam B hlam hB) (top l lam B) (answersOf (Levels.Gen.K x₀ l) lam W)
      ⟨top_inBounds ρ c x₀ l lam B, top_fits x₀ l hlam hB hW⟩ 1
  rw [cLev_top, cLam_top, clique_readTables] at run
  exact ⟨_, _, run,
    (hC₁ ρ x₀ l lam B hS.is.rho_ge hS.is.rho_lt hS.is.c_pos hS.x₀_ge hS.x₀_c hlam hB).trans (timeBound_mono ρ hS.x₀_ge l hlam hB (le_max_left _ _)),
    (hC₂ ρ x₀ l lam B hS.is.rho_ge hS.is.rho_lt hS.is.c_pos hS.x₀_ge hS.x₀_c hlam hB).trans (sizeBound_mono hS.x₀_ge l hlam hB (le_max_right _ _))⟩

end ExplicitCost
