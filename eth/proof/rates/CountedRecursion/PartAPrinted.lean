/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import LevelsStatement
import GeneralPieces.Rec.Chain
import Mathlib.Tactic

/-! # Part (a) of Theorem A, along its printed proof

The steps of part (b) take part (a) as the premise `Levels.Gen.PartA`.
`partAPrinted : Levels.Gen.PartA` puts into that form the proof of its assertions that follows the
printed proof sentence by sentence (proof/rates/GeneralPieces/Num/PartA.lean; the condition of case (ii)
of Lemma 8: proof/rates/GeneralPieces/Rec/Chain.lean), so that everything under Theorem A (b) on
counted operations rests on that proof. -/

public section

namespace ExplicitCost

/-- **Theorem A (a)**, from the sentences of its printed proof. -/
theorem partAPrinted : Levels.Gen.PartA where
  logK := GeneralPieces.PartA.logK_formula
  K_lt x₀ l hx := (GeneralPieces.PartA.K_lt_le x₀ l (by omega)).1
  K_le x₀ l hx := (GeneralPieces.PartA.K_lt_le x₀ l (by omega)).2
  e_ge ρ x₀ l hρ _ _ := by
    have := GeneralPieces.PartA.e_ge_half_pow ρ x₀ l hρ
    linarith
  e_le ρ x₀ l hρ _ hx := GeneralPieces.PartA.e_le_of_y ρ x₀ l hρ hx
  rho_pow ρ x₀ l hρ hρ1 hx := GeneralPieces.PartA.rho_pow_le ρ x₀ l (by linarith) hρ1.le (by omega)
  case_ii x₀ l hx := GeneralPieces.Chain.hoeffding_cond x₀ l hx

end ExplicitCost
