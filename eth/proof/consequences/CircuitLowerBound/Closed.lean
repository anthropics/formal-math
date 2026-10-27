/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CircuitLowerBound.Main
public import CircuitLowerBound.Small
public import CircuitLowerBound.Tab.Complete
public import CircuitLowerBound.Tab.Pack
public import CircuitLowerBound.Tab.Table
public import CircuitLowerBound.Tab.Glue
public import CircuitLowerBound.Cert.TabF
public import CircuitLowerBound.Circ.Clause
public import CircuitLowerBound.Circ.Norm
public import CircuitLowerBound.Circ.Form
public import CircuitLowerBound.Alg.Time
public import CircuitLowerBound.ENP.Restart
public import CircuitLowerBound.Oracle.Restart

/-! # The circuit lower bound for E^NP (Section 7): the interface statements `StTab`, `StForm`, `StENP'` and `StENP`

All interface statements except `StAlg`, the one that needs an algorithm for satisfiability, are
proved in the files imported here; this file assembles `stTab`, `stForm`, `stENP'` and `stENP`.
`StAlg` is proved elsewhere in this development, where all of them are fed into `corCircuits_of` of
proof/consequences/CircuitLowerBound/Main.lean. -/

public section

namespace CircuitLowerBound

/-- Every machine has a table. -/
theorem stTab : StTab := stTab_of stPack stSpec stSpecTab

/-- The formula «some clause is violated by the assignment that the circuit computes». -/
theorem stForm : StForm := stForm_of stClauseCirc

/-- The language is in E^NP, second form. -/
theorem stENP' : StENP' := stENP'_of stCertSched stCertTabF stFlip

/-- The language is in E^NP, first form. -/
theorem stENP : StENP := stRestart L0 stENP'

end CircuitLowerBound
