import Zeta23.ThmD.Sextuple.A1275.LineDecimal
import Zeta23.ThmD.Sextuple.A1275.FlatEquivalence

/-! Axiom audit for the unconditional `A = 51/4000` sextuple chain. Not imported by the library root. -/

open Zeta23.ThmD.Sextuple

-- analytic tables and adapters
#print axioms Zeta23.ThmD.Sextuple.MacroPrototype.stableMacroTable_check
#print axioms Zeta23.ThmD.Sextuple.MacroPrototype.refinementTable_check
#print axioms Zeta23.ThmD.Sextuple.MacroPrototype.improvedCatalog_check
#print axioms Zeta23.ThmD.Sextuple.MacroPrototype.improvedScalarTable_check
#print axioms Zeta23.ThmD.Sextuple.MacroPrototype.improvedConcreteLeafCheck_sound
-- physical layout and the two-level/flat reader bridge
#print axioms Zeta23.ThmD.Sextuple.MacroPrototype.improvedTopologyLayoutValid
#print axioms Zeta23.ThmD.Sextuple.MacroPrototype.improvedLeafLayoutValid
#print axioms Zeta23.ThmD.Sextuple.MacroPrototype.improvedTopologyStream_eq_packed
#print axioms Zeta23.ThmD.Sextuple.MacroPrototype.improvedPayloadStream_eq_packed
-- representative chunks, assembly nodes, root replay
#print axioms Zeta23.ThmD.Sextuple.MacroPrototype.improvedChunk0000
#print axioms Zeta23.ThmD.Sextuple.MacroPrototype.improvedChunk4476
#print axioms Zeta23.ThmD.Sextuple.MacroPrototype.improvedChunk8952
#print axioms Zeta23.ThmD.Sextuple.MacroPrototype.improvedNode0000
#print axioms Zeta23.ThmD.Sextuple.MacroPrototype.improvedNode8951
#print axioms Zeta23.ThmD.Sextuple.MacroPrototype.improvedRootReplay
#print axioms Zeta23.ThmD.Sextuple.MacroPrototype.improvedTreeCheck
#print axioms Zeta23.ThmD.Sextuple.MacroPrototype.improvedRootBox_predicate
-- concrete certificate
#print axioms Zeta23.ThmD.Sextuple.A1275.Certificate.sextuple_affine
-- conditional ledger / comparator layer
#print axioms Zeta23.ThmD.Sextuple.ImprovedAssembly.A1275.zetaSextupleLedgerInterface_of_certificate
#print axioms Zeta23.ThmD.Sextuple.ImprovedAssembly.A1275.sextupleLowerConstant_exact
#print axioms Zeta23.ThmD.Sextuple.ImprovedAssembly.A1275.sextupleLowerConstant_gt_6727837118
#print axioms Zeta23.ThmD.Sextuple.ImprovedAssembly.A1275.sextupleDyadic_6727837118_of_interfaces
#print axioms Zeta23.ThmD.Sextuple.ImprovedAssembly.A1275.sextupleCumulative_6727837118_of_interfaces
-- unconditional ledger and public endpoints
#print axioms Zeta23.ThmD.Sextuple.A1275.zetaSextupleLedgerInterface
#print axioms Zeta23.ThmD.Sextuple.A1275.zetaSextupleLedgerInterface_exactConstants
#print axioms Zeta23.ThmD.Sextuple.A1275.thmD₀_sextuple
#print axioms Zeta23.ThmD.Sextuple.A1275.thmD₀_sextuple_cumulative
#print axioms Zeta23.ThmD.Sextuple.A1275.thmD₀_sextuple_6727837118
#print axioms Zeta23.ThmD.Sextuple.A1275.thmD₀_sextuple_cumulative_6727837118
