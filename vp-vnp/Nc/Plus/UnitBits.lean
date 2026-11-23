/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Nc.Cut.Units
import Nc.Tape.Refine

/-!
# The bits of a unit
-/

namespace Nc

/-- The bits of a unit. -/
def uwBits {ub : ℕ} : UW ub → List Bool
  | none => []
  | some w => List.ofFn w

end Nc
