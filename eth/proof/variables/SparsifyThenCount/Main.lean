/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import UniformInKStatement
public import SparsifyThenCount.Defs
public import UniformInK.Top.Defs
public import VariableBound.Printed.ThmVariablesADefs
import SparsifyThenCount.Correct
import SparsifyThenCount.CorrectB
import SparsifyThenCount.CertTop
import SparsifyThenCount.CertBoth
import SparsifyThenCount.Tied
import VariableBound.MainPrinted
import VariableBound.Printed.Tied
import VariableBound.Printed.TiedDefs
import ClauseBound.Gen.Defs
import VariableBound.Paper.Decide
import VariableBound.Printed.VariablesA.Main
import VariableBound.Printed.VariablesA.Level
import VariableBound.Top.Time
import VariableBound.Top.Budget
import VariableBound.Top.CorrectB
import VariableBound.Top.Arith
import VariableBound.Top.ArithPlan
import StepSparsify.WalkCount
import StepSparsify.CertWalk
import StepSparsify.CalServes
import StepSparsify.Defs
import UniformInK.Top.Correct
import UniformInK.Top.CorrectB
import UniformInK.Top.Leaves
import ClauseBound.MainBoth
import ClauseBound.Both.TimeM
import ClauseBound.Alg.TopArith
import ClauseBound.Alg.TopVal
import ClauseBound.Alg.Decode
import CountKSatRate.Pad
import CountKSatRate.Brute

/-! # Polynomial time of the function that sparsifies with the thresholds of Step 5 and counts each output by Steps 1 to 4 as printed, and the bound of Step 6

**What is proved.**
* `certDGc`: for thresholds that serve and every polynomial-time solver, the function `ADG Θ` is
  polynomial-time, if `pick` and `slU` are.
  The certificate of the walk is that of proof/sparsification/StepSparsify
  (`StepSparsify.stCertWalkSG`, `StepSparsify.stCertNoTaut`); the count of one sparse formula is
  polynomial-time in the pad by `VariableBound.certCountDc` (Steps 1 to 4).
* `certBDGc`: the same for the merged function `ABDG Θ` and the exponent function `eBD`.
* `timeDGc`: Step 6, the number of steps of a padding machine with the exponent function `eD` is
  within the bound in n with k² in the exponent;
  it uses the arithmetic of the exponent of Steps 4 and 5 (`VariableBound.arithDc`,
  `VariableBound.stPlanLeD`), which does not know the thresholds. -/

public section

namespace SparsifyThenCount

open Groundwork PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.Both ClauseBound.ParityChecks ClauseBound.TopN UniformInK VariableBound VariableBound.Decide

/-- For thresholds that serve and every polynomial-time solver, the function `ADG Θ` is
polynomial-time, if `pick` and `slU` are. -/
theorem certDGc : StCertDG := stCertDG StepSparsify.stCertWalkSG StepSparsify.stCertNoTaut certCountDc

/-- For thresholds that serve and every polynomial-time solver, the merged function `ABDG Θ` and the
exponent function `eBD` are polynomial-time, if `pick` and `slU` are. -/
theorem certBDGc : StCertBDG := stCertBDG certDGc

/-- Step 6: the number of steps of a padding machine with the exponent function `eD` is within the
bound in n with k² in the exponent; the constant does not depend on k. -/
theorem timeDGc : StTimeD := stTimeD arithDc stPlanLeD Decode.stDecM

end SparsifyThenCount

namespace SatM

end SatM

namespace MainTheoremForms

open CountKSatRate ClauseBound.Alg

end MainTheoremForms
