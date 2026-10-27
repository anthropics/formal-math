/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThmVariables.Defs
public import ThmVariables.Bound
public import ThmVariables.PartA
public import ThmVariables.EveryMachine
import CountedToPadded.Main
import RecursionToBound.Main

/-! # Theorem D (a) with the printed hypothesis: the end theorems

The two hypotheses of EveryMachine.lean are fed in: the step from counted operations to the padding
string for the named solver (`QueryMachines.Bridge.solverOfMachineLevels`,
proof/rates/CountedToPadded) and Theorem D (a) for every machine that computes the function of Steps
1 to 5 of Appendix D (`RecursionToBound.thmVariablesAForEveryMachine`,
proof/variables/RecursionToBound).
* `solverFromMachine`: from every machine with query access as in the printed hypothesis, a solver
  with a sequence of levels.
* `partAForEveryMachine`: every machine that runs the named algorithm on the solver that the machine
  with query access gives has the bound.
* `partA`: Theorem D (a). It is taken from `partAForEveryMachine`; `partAFromThePaddingString`
  (PartA.lean) with `solverFromMachine` and `RecursionToBound.thmVariablesAWithNumberBetween` gives
  the same proposition. -/

public section

namespace ThmVariables

open QueryMachines.Bridge

/-- From every machine with query access as in the printed hypothesis of Theorem D (a): a
polynomial-time solver with a sequence of levels for the same K_ℓ and for the number in [e_ℓ, 2e_ℓ],
cut at 1. -/
theorem solverFromMachine : SolverFromMachine := solverFromMachine_of solverOfMachineLevels

/-- **Theorem D (a) for every machine that runs the named algorithm** on the solver that the machine
with query access gives. -/
theorem partAForEveryMachine : PartAForEveryMachine := partAForEveryMachineFrom solverOfMachineLevels RecursionToBound.thmVariablesAForEveryMachine

/-- **Theorem D (a)**, with the hypothesis in counted operations and table queries. -/
theorem partA : PartA := partAFromEveryMachine partAForEveryMachine

end ThmVariables
