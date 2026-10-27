/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import UniformInK.Spars.Defs
import UniformInK.Spars.Step
import UniformInK.Spars.Bound
import UniformInK.Spars.Thresholds
import UniformInK.Spars.Iface

/-! # The interface of the sparsification with the thresholds `thetaU τ`

`StIfaceU` is proved by feeding the proofs of the five statements on nodes and thresholds into
`ifaceU`. -/

public section

namespace UniformInK

/-- All that the walk of the tree needs to know about the rule on finite sets holds for the
thresholds `thetaU τ`, if 1 ≤ k and 8k ≤ τ. -/
theorem stIfaceU : StIfaceU := ifaceU stNodeRootU stNodeStepU stNodeBoundU stThrU stBetaSumU

end UniformInK
