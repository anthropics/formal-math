/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import SparsificationLemma.Geo.Defs
import SparsificationLemma.Bound
import UniformInK.Spars.Thresholds
import all UniformInK.Top.Budget

/-! # The thresholds θ 0 = 1, θ i = 4·τ^(2i−1) satisfy the conditions `ThrC`

`stThrGeo`: from `UniformInK.stThrU` (proof/sparsification/UniformInK/Spars/Thresholds.lean) and β 1 = 4.
`stDegGeo`: the bound on 2·(θ 0 + … + θ (k−1)) + 2 is `UniformInK.Budget.leafCU_add_two_le`
(proof/sparsification/UniformInK/Top/Budget.lean). -/

public section

namespace SparsificationLemma.Geo

open Finset UniformInK

/-- The thresholds `thetaU τ` with the numbers `betaSU τ` satisfy the four conditions, if 1 ≤ k and
8k ≤ τ. -/
theorem stThrGeo : StThrGeo := fun k τ hk hτ => stThrOfU k τ _ _ (by simp [betaSU]) (stThrU k τ hk hτ)

/-- 2·(θ 0 + … + θ (k−1)) + 2 ≤ τ^(2k), if 1 ≤ k and 8 ≤ τ. -/
theorem stDegGeo : StDegGeo := fun _ _ hk hτ => Budget.leafCU_add_two_le hτ hk

end SparsificationLemma.Geo
