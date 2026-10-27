/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import VariableBound.Top.ArithDefs
import VariableBound.Top.ArithNat
import VariableBound.Top.ArithNeed
public import VariableBound.Top.ArithPlan
import VariableBound.Top.ArithTop
import UniformInK.Top.ArithNat
import UniformInK.Top.ArithMaster

/-! # The exponent of the pad: the statement `StArithD`

The proofs of the interface statements of proof/variables/VariableBound/Top/ArithDefs.lean are put
together, with those of proof/sparsification/UniformInK/Top/ArithDefs.lean that do not involve the
bounds of Step 3.
The bounds of Step 3, displays (68) and (69), enter as the hypothesis `Net.StBounds`. -/

namespace VariableBound

open UniformInK

/-- Steps 4 and 5, the exponent: if the bounds of Step 3 hold (`Net.StBounds`), then for a
polynomial-time solver with a sequence of levels and 2^(−s(l)) ≤ e_l, 2^(s(l)) ≤ (2/e_l)^C there are
A and B, depending on neither k nor n:
for k ≥ 1 and n ≥ K^17 (K the number of nodes of the first level), with l the level picked for n and
s = s(l), the exponent of the plan, or n if there is none, is at most A·k²·n·e_l·(s+1), or ⌊log₂ n⌋
< B·k². -/
public theorem stArithD (hB : Net.StBounds) : StArithD :=
  Arith.stArithD_of (stNeedD (stUbD hB) (stArgD hB) (stLowerD hB) stBetaU) stPlanLeD stPlanNeedD stMasterU stDLogU stSixU stBetaU

end VariableBound
