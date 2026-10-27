/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import FixedWidthSteps.Numbers
public import FixedWidthSteps.Small
public import FixedWidthSteps.Hypothesis
public import FixedWidthSteps.Choice
public import FixedWidthSteps.Sentence
public import PairsToBound.Pairs
public import PairsToBound.Width
public import PairsToBound.FrontEnd
public import PairsToBound.Exhaust
public import TwoMachines.Main
public import RecursionToBound.Main
public import OccurM.Main
public import GeneralPieces.ThmRunningTime

/-! # The end theorems

The premises of the three implications of RouteDefs.lean are fed in: those on numbers from this
folder; the «In particular» of Theorem D (a) from
proof/variables/VariableBound/Printed/ThmVariablesA.lean; the others from
`TwoMachines`, `PairsToBound` and `RecursionToBound`. In Theorem A as a whole, parts (a), (b) and (d)
come from proof/rates/GeneralPieces/ThmRunningTime.lean and the first sentence of (c) from
proof/rates/OccurM/Main.lean. -/

public section

namespace FixedWidthSteps

/-- «Its hypothesis holds by (a) and (b)», including the clause that a number in [e_ℓ, 2e_ℓ] can be
computed, which the proviso of Theorem A (c) supplies. -/
theorem hypothesisHolds : HypothesisHolds := hypothesisHoldsFrom PairsToBound.theRecursionHasLevels chainOfInequalities

/-- The step of Theorem A (c), second sentence, that rests on the «In particular» of Theorem D (a):
its conditions hold for all but finitely many n, the other n are within the bound, and k ≤ 2 is read
as 3. -/
theorem everyChoiceCounts : EveryChoiceCounts :=
  everyChoiceCountsFrom MainTheoremForms.thmVariablesAInParticular conditionsHoldEventually smallCasesAreWithinTheBound PairsToBound.widthOr3Stmt

end FixedWidthSteps

namespace FixedWidth

open FixedWidthSteps

/-- Theorem A (c), second sentence. -/
theorem countsFromPieces : CountsFromPieces :=
  sentenceFromTheSteps RecursionToBound.thmVariablesAWithNumberBetween hypothesisHolds rateOfThePairs TwoMachines.everyTwoMachinesCanBeChosenBetween PairsToBound.frontEndAndTestExist PairsToBound.exhaustiveMachineExists
    everyChoiceCounts

/-- Theorem A, with both sentences of (c) with the printed hypotheses and quantifiers, in steps of a
Turing machine. -/
theorem runningTimesFromPieces : RunningTimesFromPieces :=
  { a := GeneralPieces.thmRunningTime_a
    b := GeneralPieces.thmRunningTime_b
    c_m := ClausesOccur.countsFromPieces
    c_n := countsFromPieces
    c_proviso := provisoHolds
    d := GeneralPieces.thmRunningTime_d }

end FixedWidth
