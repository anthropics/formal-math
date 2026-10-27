/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedRecursion.RecursionDefs

/-! # The g × g grid

The functions of proof/rates/ClauseBound/Alg/Data.lean speak of a grid with p rows and d columns,
whose «parts» are the rows or the columns. Here p = d = g, so either network of a pattern has g
nodes, each with g grid points. -/

public section

namespace ExplicitCost

open ClauseBound.Alg

/-- Both networks of the g × g grid have g nodes. -/
theorem nParts_self (g : ℕ) (tr : Bool) : nParts g g tr = g := by cases tr <;> rfl

/-- Each node has g grid points. -/
theorem nMemb_self (g : ℕ) (tr : Bool) : nMemb g g tr = g := by cases tr <;> rfl

end ExplicitCost
