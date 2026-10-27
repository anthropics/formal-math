/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import MainRoute.GeneralDefs
public import MainRoute.General
public import MainRoute.GeneralInM
import MinOfBounds.Main
import MinOfBounds.Rename
import MinOfBounds.Arith
import PairsToBound.Main
import RecursionToBound.Main

/-! # The chain for every solver: the end theorem

`routeOnEverySolver`: `routeOn_of` (General.lean) with the theorems of
proof/variables/RecursionToBound, proof/variables/PairsToBound and proof/maintheorem/MinOfBounds in
the places of its hypotheses. Neither the pieces of Appendix B nor the recursion of Appendix A
enters it. `bothBoundsOnEverySolver`: with the bound in m for every solver (`boundInMOnEverySolver`,
GeneralInM.lean), which takes from proof/rates/GeneralPieces the top level in m for a general
sequence of levels. -/

public section

namespace MainRoute

open MinOfBounds PairsToBound

/-- **The chain for every solver.** From any polynomial-time algorithm for cliques with a sequence
of levels, a computed number in [e_ℓ, 2e_ℓ] and e_ℓ = O((log K_ℓ)^(−1/2)), and any function with the
bound in m, every machine assembled in the printed way has the bound of the Main Theorem, and such a
machine exists. -/
theorem routeOnEverySolver : RouteOnEverySolver :=
  routeOn_of RecursionToBound.thmVariablesAForEveryMachine everyChoiceMeetsThmVariablesB everyExhaustiveMachineTriesAll frontEndAndTestExist exhaustiveMachineExists
    everyAlternationMeetsMinBound everyAlternationDecidesWithinMinBound renamingFrontEndExists minBoundIsTheMainTheorem

/-- **Both bounds from ONE algorithm for cliques.** For every polynomial-time algorithm for cliques
with a sequence of levels, a computed number in [e_ℓ, 2e_ℓ] and e_ℓ = O((log K_ℓ)^(−1/2)): every
machine that computes the function for the bound in m on it meets the bound in m, and every machine
assembled in the printed way from machines that compute the function of Steps 1 to 5 and the
function for the bound in m, both on it, and exhaustive counting has the bound of the Main Theorem. -/
theorem bothBoundsOnEverySolver : BothBoundsOnEverySolver := bothBounds_of routeOnEverySolver boundInMOnEverySolver

end MainRoute
