/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import UniformInKStatement
public import VariableBound.Printed.TiedDefs
public import UniformInK.Top.Defs
import VariableBound.Printed.Tied
import ClauseBound.Gen.Defs
import VariableBound.Paper.Decide
import VariableBound.Top.Time
import VariableBound.Top.Defs
import VariableBound.StepParity
import VariableBound.Family.Main
import VariableBound.Field.Family
import VariableBound.Field.Cert
import VariableBound.Params.Spec
import VariableBound.Params.Ineq
import VariableBound.Params.Cert
import VariableBound.Search.Correct
import VariableBound.Search.Cert
import VariableBound.Net.Main
import VariableBound.Count.Correct
import VariableBound.Count.Cert
import VariableBound.Top.Budget
import VariableBound.Top.Correct
import VariableBound.Top.CorrectB
import VariableBound.Top.Arith
import VariableBound.Cert.Top
import UniformInK.Top.Correct
import UniformInK.Top.CorrectB
import UniformInK.Top.Leaves
import UniformInK.Top.Budget
import UniformInK.Tree.Tree
import UniformInK.Tree.Defs
import UniformInK.Tree.Stack
import UniformInK.Spars.Main
import UniformInK.Cert.Walk
import ClauseBound.MainBoth
import ClauseBound.Both.TimeM
import ClauseBound.Alg.TopArith
import ClauseBound.Alg.TopVal
import ClauseBound.Alg.Decode
import CountKSatRate.Walk
import CountKSatRate.Pad
import CountKSatRate.Brute
import CountKSat.InOut

/-! # Lemmas for the bound in n of Appendix D with Steps 1 to 4 as printed

This file holds lemmas of the Lean proof of the bound in n of Appendix D in which each sparse
formula is counted by Steps 1 to 4 as printed.
* `certCountDc`: the count of one sparse formula is polynomial-time in the pad.
* `expBDc`: the exponent `eBD` is at most `eD` and, if all variables occur and there is a clause, at
  most the exponent of the algorithm for the bound in m.
* `arithDc`: Steps 4 and 5, a bound on the exponent of a plan. -/

public section

namespace VariableBound

open Groundwork PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.Both ClauseBound.ParityChecks UniformInK VariableBound.Decide

/-- The count of one sparse formula is polynomial-time in the pad, jointly in the width. -/
theorem certCountDc : StCertCountD := stCertCountD Net.Main.certEvD stCertSearchD Fld.Cert.stCertFamD stCertParam

/-- For k ≥ 1 and a k-CNF: the exponent `eBD` is at most `eD`, and, if all variables occur and there
is a clause, at most the exponent of the algorithm for the bound in m. -/
theorem expBDc : StExpBD := stExpBD (stAllOccU Decode.stDecM) Decode.stDecM

/-- Steps 4 and 5: the exponent of a plan, or n if there is none, is at most A·k²·n·e_l·(s+1), or
⌊log₂ n⌋ < B·k²; under the hypotheses on the solver and on s(l) listed at `StArithD`. -/
theorem arithDc : StArithD := stArithD Net.Main.bounds

end VariableBound

namespace SatM

end SatM
