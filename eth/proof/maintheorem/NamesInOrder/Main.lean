/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import NamesInOrder.Defs
public import NamesInOrder.Arith
public import NamesInOrder.Chain
public import NamesInOrder.General
import MainRoute.GeneralMain
import PairsToBound.Main

/-! # The Main Theorem when the variables are x₀ … x_(n−1) and each occurs: the end theorems

The theorems of Chain.lean with the inequalities of Arith.lean, the chain for every solver
(`MainRoute.bothBoundsOnEverySolver`), the statement on the pairs and Θ
(proof/variables/PairsToBound) in the places of their hypotheses. The inequalities and
`boundInMWithoutThePolynomial` are in Arith.lean, `builtIsAssembledDirectly` in Chain.lean,
`generalFormFollows` and `generalFormFollowsAsPropositions` in General.lean. -/

public section

namespace NamesInOrder

open MainRoute PairsToBound

/-- **The main statement**: Corollary 11 from the first sentence of Theorem A (c) and Theorem D (b),
for every machine. -/
theorem everyDirectAlternationMeetsTheBound : EveryDirectAlternationMeetsTheBound := everyDirectAlternation_of alternationCostGoesIntoC

/-- The chain for every solver. -/
theorem onEverySolver : OnEverySolver := onEverySolver_of bothBoundsOnEverySolver boundInMWithoutThePolynomial everyDirectAlternationMeetsTheBound

/-- The chain for all pieces of Appendix B. -/
theorem forAllPieces : ForAllPieces := forAllPieces_of onEverySolver thePairsSatisfyTheHypothesis thetaOfThePairs

/-- **The Main Theorem**. -/
theorem mainTheoremHolds : MainTheoremHolds := (closed_of forAllPieces).1

/-- **Corollary 11**. -/
theorem corMinHolds : CorMinHolds := (closed_of forAllPieces).2

/-- **The first sentence of Theorem A (c)**, at α′ = 1/2. -/
theorem boundInMHolds : BoundInMHolds := boundInMHolds_of forAllPieces

end NamesInOrder
