/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.Base
public import CountedRecursion.BothNetworks
public import CountedRecursion.ChildIsGood
public import CountedRecursion.ProcedureCost
public import CountedRecursion.SolverStep
public import CountedRecursion.Meets
public import CountedRecursion.Expansion
public import CountedRecursion.Totals
public import CountedRecursion.CaseTwo
public import CountedRecursion.LabelCrude
public import CountedRecursion.TotalCount
public import CountedRecursion.TotalRoom
public import CountedRecursion.RoomWithin
public import CountedRecursion.RecursionDefs
public import CountedRecursion.Answers
public import CountedRecursion.PolyAll
public import CountedRecursion.EndCounted
public import CountedRecursion.EndPlugged
public import CountedRecursion.EndSolves
public import ExplicitCost.Cost
public import ExplicitCost.GroupingCall
public import ExplicitCost.GroupingNumbers
public import Value.End
public import Tower.TowerRuns
public import PiecesCounted.Oracle
public import PiecesCounted.Assume

/-! # Theorem A (b) on counted operations: the end theorems

Every statement «… From» of RecursionDefs.lean is an implication from statements of other steps or
of other parts of this development. Each is fed with theorems, here or in the file of its step, so
that every step and the theorem itself stand without hypotheses.

**Fed here**, in the order of the printed proof: `ChildIsGoodFrom`, `ProcedureCostFrom`,
`SolverStepFrom`, `RecursionMeetsFrom`, `RecursionCountedUpToFrom`, `RecursionPluggedFrom`,
`RecursionSolvesFrom`.
**Fed in the file of the step:** `BothNetworksFrom` (BothNetworks.lean); `ChainBaseFrom`,
`ChainExponentFrom` (Chain.lean); `BoundBelowFrom` (LevelBound.lean); `CountBaseFrom`
(CountBase.lean); `CountStepFrom` (CountStep.lean); `TotalCountFrom` (TotalCount.lean);
`TotalRoomFrom` (TotalRoom.lean); `RoomIsWithinTheBoundFrom` (RoomWithin.lean); `RecursionPolyFrom`,
`RecursionWithPolyFrom` (PolyEnd.lean).
**Proved without premises, in their own files:** `solverBase`, `expansion`, `patternsFew`,
`pairIsProduct`, `listsAgree`, `totalsAre`, `smallerTotal`, `caseTwoApplies`, `labelBound`,
`labelCrude`, `crudeBounds`, `chainLabel`, `chainLevels`, `exponentFits`, `readAsRuns`,
`readAsPoly`, `pricesScale`, `numbersRun`, `numbersPoly`, `recursionPoly`. Of these, `readAsPoly`
and `numbersPoly` are premises of no «… From»; they are used inside the certificates
(PolyRules.lean, PolySolver.lean).
**Where «Crude bounds give L ≤ N + 1» is used:** for the L of a call, in `procedureCostFrom`, where
the cost of an entry asks L ≤ 2gP (`labelCrude`); at the bounds along the recursion the same clause
is part of `chainLabel`, from which `chainBase` gets K(L + B') ≤ Ξ^{c+5}.
**Used as lemmas and not as premises:** e_ℓ ≥ 0 in `recursionSolvesFrom`
(`GeneralPieces.PartA.e_ge_half_pow`, a sentence of the printed proof of part (a)); `listsAgree` in
`totalsAre` and `smallerTotal`, which have no «… From».
**From other parts of this development:** Lemma 8 up to the call, its L, and the cost of an entry
(`groupingWithCall`, `labelLengthIsL`, `entryCostExplicit`: proof/rates/ExplicitCost); «whose value
is that of the network» (`Value.stValueEqualsZ`); the tower (`QueryMachines.Tower.towerRuns`,
`towerPoly`, `costShape`); the rule of substitution (`QueryMachines.stSubstWithin`); from the oracle
of the pieces to their algorithm (`PiecesCounted.oracleFromAlgorithm`); part (a) of the theorem
along its printed proof (`partAPrinted`, PartAPrinted.lean, from
proof/rates/GeneralPieces/Num/PartA.lean). -/

public section

namespace ExplicitCost

open QueryMachines

/-- A call goes to the (K_ℓ, L)-clique of the groups of the network with the smaller total, for some
function ι from the rectangles to the indices of the pieces. -/
theorem childIsGood : ChildIsGood := childIsGoodFrom groupingWithCall labelLengthIsL entryCostExplicit Value.stValueEqualsZ bothNetworks totalsAre smallerTotal caseTwoApplies labelBound

/-- One entry of the callee's tables. -/
theorem procedureCost : ProcedureCost := procedureCostFrom groupingWithCall labelLengthIsL caseTwoApplies entryCostExplicit bothNetworks labelCrude crudeBounds stSubstWithin

/-- The solver at a level ℓ + 1. -/
theorem solverStep : SolverStep := solverStepFrom numbersRun expansion patternsFew groupingWithCall labelLengthIsL Value.stValueEqualsZ bothNetworks caseTwoApplies crudeBounds stSubstWithin

/-- The solver and the procedure meet the specification. -/
theorem recursionMeets : RecursionMeets := recursionMeetsFrom solverBase solverStep procedureCost childIsGood

/-- Theorem A (b) with the pieces as a priced oracle that is asked only about strings of at most Λ
bits. -/
theorem recursionCountedUpTo : RecursionCountedUpTo := recursionCountedUpToFrom recursionMeets totalCount totalRoom Tower.towerRuns

/-- **Theorem A (b), with the pieces computed by their algorithm.** -/
theorem recursionPlugged : RecursionPlugged := recursionPluggedFrom recursionCountedUpTo pricesScale PiecesCounted.oracleFromAlgorithm

/-- **Theorem A (b)**, in the one form that is also the hypothesis of Theorem D (a). -/
theorem recursionSolves : RecursionSolves := recursionSolvesFrom recursionPlugged roomIsWithinTheBound readAsRuns recursionWithPoly

end ExplicitCost
