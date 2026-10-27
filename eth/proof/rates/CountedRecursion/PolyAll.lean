/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.PolyEnd
public import ExplicitCost.GroupingPoly
public import Tower.PolyTower
import Mathlib.Tactic

/-! # The certificates, closed

`recursionPoly : RecursionPoly` and `recursionWithPoly : RecursionWithPoly`, from PolyEnd.lean, the
certificate of the procedure of the lemma on groupings up to its call (`groupingPoly`,
proof/rates/ExplicitCost/GroupingPoly.lean) and that of the tower (`Tower.towerPoly`,
proof/machines/Tower/PolyTower.lean). -/

public section

namespace ExplicitCost

open Groundwork QueryMachines Printed

/-- **`RecursionPoly`**: the solver and the procedure have polynomial-time steps, one certificate
each for all levels. -/
theorem recursionPoly : RecursionPoly := recursionPoly_of groupingPoly.1

/-- The one machine for all levels has polynomial-time steps. -/
theorem recursion_poly (c x₀ : ℕ) : (recursion c x₀).PolyTimeSteps := recursionPolyFrom Tower.towerPoly recursionPoly c x₀

/-- **`RecursionWithPoly`**: so has the machine with the algorithm of the pieces built in, and the
algorithm of the theorem. -/
theorem recursionWithPoly : RecursionWithPoly := recursionWithPolyFrom recursion_poly

end ExplicitCost
