/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import CountedToPadded.Defs
import Printed.Coding

/-! # The value of the clique with tables that are written out

Proof of `TablesValue` (Defs.lean): it is `Printed.stCliqueValue`, the sentence after Definition 3,
for the tables read from T; the two ways to name an entry agree by definition. -/

public section

namespace QueryMachines.Bridge

open Groundwork Groundwork.Prog PaddedDescent.F Eight.SecNetworks Printed

/-- The value of the clique of Definition 3 with the tables read from T is the value of the instance
(λ, T). -/
theorem tablesValue : TablesValue := by
  intro K lam T hK hlam
  refine (Printed.stCliqueValue K lam (fun w z => entry T (w, z)) hK hlam).trans ?_
  show Inst.ZW lam [] (listTables K fun w z => entry T (w, z)) = Inst.ZW (unary lam).length [] (instOf T)
  rw [show (unary lam).length = lam from List.length_replicate]
  rfl

end QueryMachines.Bridge
