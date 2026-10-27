/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Printed.GroupingProcs
public import Printed.GroupingRun
public import Printed.GroupingPoly
import Mathlib.Tactic

/-! # Lemma 1 from Definition 4

The pieces come from proof/threesat/Printed/GroupingProcs.lean (`stOnProcedures`),
GroupingEntry.lean (`stEntryCost`), GroupingRun.lean (`stGroupingTiedOf`), GroupingPoly.lean
(`stGroupingPoly`). Here they are put together.
* `stGroupingTied_of`: Lemma 1 for the algorithm of its proof, from three statements proved in other
  folders: «a good grouping exists … fix the first good one» (`Eight.ViaGrouping.StSearch`), the run
  of the search (`Exits.StSearchStops`) and «so the value equals Z» (`Value.StValueEqualsZ`);
* `groupingLemma_of`: **Lemma 1** as printed, from the form for the named machine. -/

public section

namespace Printed

open QueryMachines

/-- Lemma 1 for the algorithm of its proof, from a proof of «a good grouping exists … fix the first
good one», the run of the search and «so the value equals Z». -/
theorem stGroupingTied_of (hS : Eight.ViaGrouping.StSearch) (hStops : Exits.StSearchStops) (hV : Value.StValueEqualsZ) : StGroupingTied := stGroupingTiedOf hS hStops stEntryCost hV stSubst

/-- **Lemma 1**, from the form for the named machine: the machine is `groupingMachine K (3K⁸) M`,
for a machine M that witnesses that (K, e) is achievable. -/
theorem groupingLemma_of (h : StGroupingTied) : GroupingLemma := fun K e ⟨hK, h0, M, Cc, hp, hM⟩ =>
  let ⟨C₁, hC⟩ := h K e M Cc hK h0 hM
  ⟨groupingMachine K (3 * K ^ 8) M, C₁, stGroupingPoly K _ M hp, hC⟩

end Printed
