/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Price.Basic

/-!
# The flat case, in the form in which the later sections use it
-/

namespace Nc.Flag

open Nc.Price

/-- The flat case: all finite families of points of Euclidean spaces, with their distances, are prices. -/
def CaseOne (K : Type) [Field K] : Prop :=
  ∀ (k : ℕ) (V : Type) [Finite V] (E : V → EuclideanSpace ℝ (Fin k)),
    IsPrice K fun a b => dist (E a) (E b)

end Nc.Flag
