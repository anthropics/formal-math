/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedToPadded.Defs
import CountedToPadded.RunFor
import CountedToPadded.TablesValue
import CountedToPadded.Tables
import CountedToPadded.Need
import CountedToPadded.Pick
import CountedToPadded.SolverPoly
import CountedToPadded.Levels
import QueryMachines.Runs

/-! # The end theorems

The premises of the implications of Defs.lean are fed in. -/

public section

namespace QueryMachines.Bridge

/-- The solver that a machine gives is polynomial-time. -/
theorem solverOfMachinePoly : SolverOfMachinePoly := solverOfMachinePolyFrom runForPoly

/-- **The main statement**: for every machine M with query access and polynomial-time steps that
evaluates the cliques of all levels within the printed bound, the named solver is polynomial-time
and has a sequence of levels. -/
theorem solverOfMachineLevels : SolverOfMachineLevels :=
  solverOfMachineLevelsFrom stPlug runForIsRight tablesValue bitsOfTablesFacts cutNumberFacts needSuffices needIsSmall solverOfMachinePoly pickOfFacts

end QueryMachines.Bridge
