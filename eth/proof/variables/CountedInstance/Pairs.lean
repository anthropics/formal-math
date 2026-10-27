/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedInstanceStatement
import CountedToPadded.GenLevels
import PairsToBound.Pairs
import GeneralPieces.Num.PartA
import GeneralPieces.Num.PartAUse
import GeneralPieces.Num.Asymptotic
import GeneralPieces.Num.Between
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # The clauses on numbers alone

For ρ = 1/√2, every x₀ ≥ 18 and every C₀ ≥ 10, from part (a) of Theorem A, proved here along its
proof in the paper (`GeneralPieces.PartA.thmRunningTime_a`):

* K_ℓ ≥ 2, K_ℓ < K_(ℓ+1) ≤ K_ℓ^{10} ≤ K_ℓ^{C₀}, (log K_ℓ)^{−C₀} ≤ 1/log K_ℓ ≤ e_ℓ ≤ 1
  (`GeneralPieces.PartAUse`);
* K_ℓ is computed by the named program (`CliqueLevels.levelsAreComputed`);
* the rational number `GeneralPieces.Between.num` ℓ / `GeneralPieces.Between.den` ℓ, computed from
  ℓ, which serves as the number in [e_ℓ, 2e_ℓ] of the hypothesis of Theorem D (a), lies between 0.85·ρ^ℓ
  and ρ^ℓ (`GeneralPieces.Between.between_half`), and every such number lies in [e_ℓ, 2e_ℓ]
  (`GeneralPieces.Asymptotic.between`);
* e_ℓ ≤ 0.85·√(3x₀+6)/√(log K_ℓ) (`PairsToBound.thetaOfThePairs`) ≤ (3x₀+6)/√(log K_ℓ). -/

public section

namespace CountedInstance

open Groundwork

/-- The clauses of the hypothesis of Theorem D (a) that speak of numbers alone, for the pairs (K_ℓ,
e_ℓ) at ρ = 1/√2. -/
theorem thePairsMeetTheClauses : ThePairsMeetTheClauses := by
  intro x₀ C₀ hx hC
  obtain ⟨hρ, hρ1⟩ := PairsToBound.half_le_inv_sqrt_two
  have hA := GeneralPieces.PartA.thmRunningTime_a (1 / Real.sqrt 2) x₀ hρ hρ1 hx
  refine ⟨⟨by omega, fun l => GeneralPieces.PartAUse.two_le_K hA l, fun l => (hA.K_lt_le l).1,
    fun l => (hA.K_lt_le l).2.trans (Nat.pow_le_pow_right (by have := GeneralPieces.PartAUse.two_le_K hA l; omega) hC),
    fun l => GeneralPieces.PartAUse.inv_logK_pow_le_e hA hρ (by omega) l C₀ (by omega), fun l => GeneralPieces.PartAUse.e_le_one hA (by linarith) hρ1.le l⟩,
    CliqueLevels.levelsAreComputed x₀, ⟨?_, fun l => ?_⟩, fun l => ?_⟩
  · exact GeneralPieces.Between.num_den_polyT.comp (PolyT.fst PolyT.id')
  · have hb := GeneralPieces.Between.between_half l
    have h := GeneralPieces.Asymptotic.between (1 / Real.sqrt 2) x₀ l _ hρ hx hb.1 hb.2
    have e : (Printed.unary l).length = l := List.length_replicate
    change Levels.Gen.e (1 / Real.sqrt 2) x₀ l ≤ (GeneralPieces.Between.num (Printed.unary l).length : ℝ) / (GeneralPieces.Between.den (Printed.unary l).length : ℝ) ∧
      (GeneralPieces.Between.num (Printed.unary l).length : ℝ) / (GeneralPieces.Between.den (Printed.unary l).length : ℝ) ≤ 2 * Levels.Gen.e (1 / Real.sqrt 2) x₀ l
    rw [e]
    exact h
  · obtain ⟨-, -, -, -, -, h6⟩ := PairsToBound.thetaOfThePairs x₀ l hx
    have hx0 : (0 : ℝ) ≤ x₀ := Nat.cast_nonneg _
    have hs0 := Real.sqrt_nonneg (3 * (x₀ : ℝ) + 6)
    have hs : Real.sqrt (3 * (x₀ : ℝ) + 6) ≤ 3 * (x₀ : ℝ) + 6 := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    refine h6.trans (div_le_div_of_nonneg_right ?_ (Real.sqrt_nonneg _))
    push_cast
    linarith

end CountedInstance
