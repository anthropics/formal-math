import Zeta23.ThmD.Sextuple.A1285.TreeWords
import Zeta23.ThmD.Sextuple.Macro.Layout

/-! Physical layout of the `A = 257 / 20000` certificate words: the audited flat predicates for the
concatenations of the two-level arrays. -/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

noncomputable section

namespace Zeta23.ThmD.Sextuple.MacroPrototype.A1285

def improvedTopologyWords : Array ℕ :=
  ⟨(improvedTopologyBlocks.toList.map Array.toList).flatten⟩

def improvedLeafBlocks : Array ℕ :=
  ⟨(improvedLeafBlockGroups.toList.map Array.toList).flatten⟩

lemma improvedTopologyLayoutBool_check :
    topologyLayoutBool improvedTokenCount improvedTopologyWords = true := by
  decide +kernel

lemma improvedLeafLayoutBool_check :
    leafLayoutBool improvedLeafCount improvedLeafBlocks = true := by
  decide +kernel

theorem improvedTopologyLayoutValid :
    PackedTopologyLayoutValid improvedTokenCount improvedTopologyWords :=
  topologyLayoutBool_sound improvedTopologyLayoutBool_check

theorem improvedLeafLayoutValid :
    PackedLeafLayoutValid improvedLeafCount improvedLeafBlocks :=
  leafLayoutBool_sound improvedLeafLayoutBool_check

#print axioms improvedTopologyLayoutValid
#print axioms improvedLeafLayoutValid

end Zeta23.ThmD.Sextuple.MacroPrototype.A1285

end
