/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Printed.ThmVariablesADefs
import VariableBound.Printed.VariablesA.Level
import VariableBound.Printed.VariablesA.StepSparsify
import VariableBound.Printed.VariablesA.Setting
import VariableBound.Printed.VariablesA.Main
import VariableBound.Params.Ineq
import UniformInK.Top.Correct
import UniformInK.Top.Defs
import ClauseBound.ParityChecks.CertPar
import ClauseBound.TopN.Cert
import ClauseBound.ParityChecks.CertOL
import UniformInK.Cert.Top
import UniformInK.Tree.Tree
import UniformInK.Tree.Defs
import UniformInK.Tree.Stack
import UniformInK.Spars.Main
import UniformInK.Cert.Walk
import UniformInK.Top.Leaves
import UniformInK.Top.Budget
import UniformInK.Top.ArithDefs
import FixedWidthVariableBoundStatement
import ClauseBound.ParityChecks.MasterOL
import ClauseBound.Alg.Decode
import ClauseBound.Alg.CertTopNet
import PaddedDescent.Col.CertG
import PaddedDescent.F.CertMark
import CountKSatRate.Walk
import CountKSatRate.Pad
import CountKSatRate.Brute
import CountKSat.InOut

/-! # Theorem D (a) of Appendix D: its last sentence and a fact of Step 5

Two statements of proof/variables/VariableBound/Printed/ThmVariablesADefs.lean, collected here in
the namespace `MainTheoremForms` under the names of the statements: the last sentence of Theorem D (a)
and the bound k·log n ≤ e·n of Step 5. -/

public section

namespace MainTheoremForms

open Groundwork PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.ParityChecks UniformInK VariableBound.VariablesA

/-- Theorem D (a), last sentence: if e_ℓ ≤ c·(log K_ℓ)^(−α′) for all ℓ, with α′ > 0, a machine with
the bound of Theorem D (a) takes at most 2^{C'·k²·n·log log n/(log n)^α′} steps, for n ≥ K₀^17 and 3
≤ k ≤ (log n)^(1/4). -/
theorem thmVariablesAInParticular : ThmVariablesAInParticular := VariableBound.VariablesA.thmVariablesAInParticular

/-- Step 5: k·log n ≤ e·n for n ≥ n₁(C₀), k ≤ (log n)^(1/4) and e ≥ (log n)^(−C₀). -/
theorem stepSparsifyLarge : StepSparsifyLargeStmt := VariableBound.VariablesA.stepSparsifyLarge

end MainTheoremForms
