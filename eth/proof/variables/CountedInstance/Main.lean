/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedInstanceStatement
import CountedInstance.Pairs
import CountedToPadded.GenLevels
import PiecesCounted.Half
import PiecesCounted.Assume
import CountedRecursion.Main

/-! # The recursion of Theorem A (b) on the pieces of Appendix B meets the hypothesis of Theorem D (a)

* `theRecursionMeetsTheHypothesisFrom`: Theorem B in counted operations, for the functions of its
  proof, gives a constant c and pieces D₀ with parameters (1/√2, c). «We may and do assume …» gives
  pieces D with parameters (1/√2, c + 2), the same d, 𝓘 and A_s, and all numbers of bits at most 2λ.
  Take x₀ = c + 18, so that x₀ ≥ 18 and 2^{x₀} ≥ c + 7 = (c + 2) + 5. Theorem A (b) in counted
  operations gives a constant C₀, which depends on c + 2 only, for the machine
  `cliqueMachine (c + 2) x₀ Alg`. The constant is replaced by the larger of C₀ and 10, and the
  clauses on numbers hold for it.
* `theRecursionMeetsTheHypothesis`: with the five premises proved. -/

public section

namespace CountedInstance

open Groundwork QueryMachines Printed ExplicitCost

/-- How: from Theorem B, «We may and do assume …» and Theorem A (b), all in counted operations, and
the clauses on numbers. -/
theorem theRecursionMeetsTheHypothesisFrom : TheRecursionMeetsTheHypothesisFrom := by
  intro hB hM hR hG hP
  obtain ⟨c, D₀, Alg₀, h₀, hties⟩ := hB
  obtain ⟨D, Alg, hD, hsame⟩ := hM _ c D₀ Alg₀ h₀
  obtain ⟨C₀, hC₀⟩ := hR (c + 2)
  have hx : 18 ≤ c + 18 := by omega
  have hx2 : c + 7 ≤ 2 ^ (c + 18) := by
    have := Nat.lt_two_pow_self (n := c + 18)
    omega
  have hshort : ∀ lam tr i, D.cap lam tr i ≤ 2 * lam := fun lam => (hsame lam).2.2.2
  obtain ⟨hpoly, hsolves⟩ := hC₀ _ (c + 18) D Alg hD ⟨hD.is, hshort, hx, by omega⟩
  obtain ⟨hL, hK, hN, hE⟩ := hP (c + 18) (max C₀ 10) hx (le_max_right _ _)
  refine ⟨c, c + 18, max C₀ 10, D, Alg, hD, hshort, fun lam hlam => ?_, hx, hx2, hpoly,
    (hG _ _ _ C₀ (max C₀ 10) (fun l => by have := hL.K_two l; omega) (le_max_left _ _)).1 hsolves, hL, hK, hN, hE⟩
  obtain ⟨mu, hmu, hI, hd, hA⟩ := hties lam hlam
  obtain ⟨e1, e2, e3, -⟩ := hsame lam
  refine ⟨mu, hmu, by rw [e2, hI], by rw [e1, hd], fun s hs x y u v => ?_⟩
  rw [e2] at hs
  rw [e3]
  exact (hA s hs).1 x y u v

/-- **«The pairs (K_ℓ, e_ℓ) of (40), for the pieces of Appendix B, satisfy this hypothesis»**, in
counted operations, for the named machine. -/
theorem theRecursionMeetsTheHypothesis : TheRecursionMeetsTheHypothesis :=
  theRecursionMeetsTheHypothesisFrom PiecesCounted.halfPieces PiecesCounted.mayAssume recursionSolves CliqueLevels.solvesGrowsWithTheConstant thePairsMeetTheClauses

end CountedInstance
