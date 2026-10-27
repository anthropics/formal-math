/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import RecursionToBound.Defs
public import RecursionToBound.Numbers
public import RecursionToBound.OneOutput
public import RecursionToBound.Exponent
public import RecursionToBound.Cert.Top
public import RecursionToBound.Guard
public import RecursionToBound.Tree
public import RecursionToBound.Correct
public import RecursionToBound.End

/-! # Theorem D (a) along the printed Step 5: the end theorems

The statements of proof/variables/RecursionToBound/Defs.lean and where each is proved.
* The numbers of Step 5 (Numbers.lean): `occBoundIsThePrinted`, `boundsGrowWithDelta`,
  `cutOffIsIdle`, `outputsAreWithinTheSetting`.
* The cost (OneOutput.lean, Exponent.lean): `oneOutputCost`, `walkCost`, `exponentIsWithinTheBound`.
* The tree and the code (Tree.lean): `walkTreeIsSparsify`, `outputsAreFew`, `ownDeltaIsBounded`,
  `widthOnTheCode`.
* The guard (Guard.lean): `planFailsOnlyAboveN`. Polynomial time (Cert/Top.lean):
  `countIsPolynomialTime`.
* Here: `countIsRight` (from `outputsAreWithinTheSetting`, `cutOffIsIdle` and `planFailsOnlyAboveN`,
  by Correct.lean), `thmVariablesAForEveryMachine` (from `countIsRight`, `countIsPolynomialTime`,
  `planFailsOnlyAboveN` and `widthOnTheCode`, by End.lean) and `thmVariablesAWithNumberBetween`
  (from `thmVariablesAForEveryMachine`). -/

public section

namespace RecursionToBound

/-- The function is right in the range of Theorem D (a). -/
theorem countIsRight : CountIsRight := countIsRight_of outputsAreWithinTheSetting cutOffIsIdle planFailsOnlyAboveN

/-- **Theorem D (a) for every machine that computes the named function**: for all large n₁ some
machine with finite alphabets computes `count S n₁ Q.pick num` with the exponent
`expo S n₁ Q.pick num`, and every machine that does has the bound of Theorem D (a). -/
theorem thmVariablesAForEveryMachine : ThmVariablesAForEveryMachine :=
  thmVariablesAForEveryMachine_of countIsRight countIsPolynomialTime planFailsOnlyAboveN widthOnTheCode

/-- **Theorem D (a), with the printed clause on the number in [e_ℓ, 2e_ℓ]**. -/
theorem thmVariablesAWithNumberBetween : ThmVariablesAWithNumberBetween := thmVariablesAWithNumberBetween_of thmVariablesAForEveryMachine

end RecursionToBound
